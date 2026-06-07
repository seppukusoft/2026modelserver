import Papa from "papaparse";
import { readFileSync } from "fs";
import { resolve, dirname } from "path";
import { fileURLToPath } from "url";
import "dotenv/config";

const __dirname = dirname(fileURLToPath(import.meta.url));
const outPath = process.argv.includes("--out")
    ? process.argv[process.argv.indexOf("--out") + 1]
    : resolve(__dirname, "results_"+ new Date().toISOString().split('T')[0] + ".json");

const colorMapping = {
    solidR: "#d22532", likelyR: "#ff5865", leanR: "#ff8b98", tiltR: "#cf8980",
    tiltD:  "#848fb3", leanD:   "#90acfc", likelyD: "#577ccc", solidD: "#244999",
    tiltI:  "#c4aeee", leanI:   "#b57edc", likelyI: "#a14fd2", solidI: "#8e20c7",
    tiltL:  "#fff9c2", leanL:   "#fff1a0", likelyL: "#ffe66e", solidL: "#ffdb00",
    noElec: "#575757",
};

function netStr(gains, losses, party, color) {
    const net = (gains[party] || 0) - (losses[party] || 0);
    if (net === 0) return "";
    const arrow = net > 0
        ? `<span style="color:#22c55e">▲ ${net}</span>`
        : `<span style="color:#ef4444">▼ ${Math.abs(net)}</span>`;
    return `<span style="color:${color}">${arrow}</span>`;
}

const _ratingsPromiseCache = Object.create(null);

function buildRatingsMap(ratingsText) {
    const parsed = Papa.parse(ratingsText, { header: true, dynamicTyping: true });
    const map = new Map();
    for (const row of parsed.data) {
        if (!row.Pollster) continue;
        const biasMatch = String(row["Mean-reverted bias"] || "").match(/@@(-?[\d.]+)/);
        const bias = biasMatch ? parseFloat(biasMatch[1]) : 0;
        const ppm  = parseFloat(row["Predictive Plus-Minus"]) || 0;
        const key  = row.Pollster.toLowerCase().replace(/[^a-z0-9]/g, "");
        map.set(key, { ppm, bias });
    }
    return map;
}

function findPollsterRating(pollsterName, ratingsMap) {
    if (!pollsterName || !ratingsMap.size) return null;
    const norm = pollsterName.toLowerCase().replace(/[^a-z0-9]/g, "");
    let bestMatch = null, bestLen = 0;
    for (const [key, rating] of ratingsMap) {
        if ((norm.includes(key) || key.includes(norm)) && key.length > bestLen) {
            bestLen = key.length;
            bestMatch = rating;
        }
    }
    return bestMatch;
}

function applyBiasCorrection(responses, bias) {
    if (!bias) return responses;
    return responses.map(r => {
        const correction = (r.party === "DEM" || r.party === "WFP") ? -(bias / 2)
                         :  r.party === "REP"                        ?  (bias / 2)
                         : 0;
        return correction ? { ...r, pct: Math.max(0, (r.pct || 0) + correction) } : r;
    });
}

function renormalizeEstimates(estimates) {
    let sum = 0;
    for (const c in estimates) sum += estimates[c].pct;
    if (!sum || sum <= 0) return estimates;
    const scale = 100 / sum;
    const out = Object.create(null);
    for (const c in estimates) {
        out[c] = { pct: estimates[c].pct * scale, party: estimates[c].party };
    }
    return out;
}

function randomNormal(mean = 0, sigma = 1) {
    let u = 0, v = 0;
    while (!u) u = Math.random();
    while (!v) v = Math.random();
    return mean + sigma * Math.sqrt(-2 * Math.log(u)) * Math.cos(2 * Math.PI * v);
}

function monteCarloMulti(candidates, sigma, iterations = 25000) {
    const names = Object.keys(candidates);
    const n = names.length;
    const wins  = new Int32Array(n);
    const draws = new Float64Array(n);
    const means = new Float64Array(names.map(k => candidates[k]));

    for (let i = 0; i < iterations; i++) {
        let sum = 0;
        for (let j = 0; j < n; j++) {
            const v = Math.max(0, randomNormal(means[j], sigma));
            draws[j] = v;
            sum += v;
        }
        if (!sum) continue;
        let best = 0, bestPct = 0;
        for (let j = 0; j < n; j++) {
            const pct = draws[j] / sum;
            if (pct > bestPct) { bestPct = pct; best = j; }
        }
        wins[best]++;
    }

    const result = Object.create(null);
    for (let i = 0; i < n; i++) result[names[i]] = wins[i] / iterations;
    return result;
}

async function runRacePipeline(url, config) {
    const {
        excludeRe,
        primaryWinners,
        pviMap,
        pviOffset = 2.75,
        notGenYet,
        fixKnownIndependents,
        getRegionFromRow,
        regionKey,
        extraRowFilter,
        minPolls = 2,
        defaults = {},
        rcvRegions = [],
        ratingsUrl,
        excludeQuestionIds = []
    } = config;

    const notGenYetSet  = new Set(notGenYet);
    const rcvRegionsSet = new Set(rcvRegions);
    const excludeQuestionIdsSet = new Set(excludeQuestionIds);
    const partyCache    = Object.create(null);
    const lastNameCache = new Map();

    function normalizeParty(p) {
        if (!p) return "IND";
        const key = String(p).toUpperCase();
        return partyCache[key] ??= (
            key.includes("DEM") ? "DEM" :
            key.includes("REP") ? "REP" :
            key.includes("LIB") ? "LIB" :
            "IND"
        );
    }

    function getLastName(name) {
        if (!name) return "";
        if (lastNameCache.has(name)) return lastNameCache.get(name);
        const ln = name.toLowerCase().replace(/[^a-z\s]/g, "").trim().split(/\s+/).pop();
        lastNameCache.set(name, ln);
        return ln;
    }

    function applyPartisanSponsorDiscount(poll) {
        const sp = poll.sponsorParty;
        if (sp === "IND") return poll.responses;
        return poll.responses.map(r =>
            r.party === sp ? { ...r, pct: (r.pct || 0) * 0.85 } : r
        );
    }

    const someoneElseRe = /someone else/i;
    const regionsWithNamed3p = new Set();

    function normalizeResponses(poll) {
        if (poll._normalized) return poll._normalized;
        const discounted  = applyPartisanSponsorDiscount(poll);
        const biasCorrect = applyBiasCorrection(discounted, poll.pollsterBias);
        const excludeSomeoneElse = regionsWithNamed3p.has(poll[regionKey]);
        let sum = 0;
        const cleaned = [];
        for (const r of biasCorrect) {
            if (!excludeRe.test(r.candidate) &&
                !(excludeSomeoneElse && someoneElseRe.test(r.candidate))) {
                cleaned.push(r);
                sum += r.pct || 0;
            }
        }
        if (!sum) return (poll._normalized = cleaned);
        const scale = 100 / sum;
        return (poll._normalized = cleaned.map(r => ({ ...r, pct: r.pct * scale })));
    }

    function groupByPollId(rows, ratingsMap) {
        const polls = Object.create(null);
        const pollsterCache = new Map();
        const now = Date.now();

        for (const row of rows) {
            if (!row.poll_id || !row.question_id) continue;
            if (excludeQuestionIdsSet.has(row.question_id)) continue;
            const key = row.poll_id + "_" + row.question_id;
            let poll = polls[key];
            if (!poll) {
                const methodology = row.methodology || "";
                const methodologyMultiplier =
                    methodology.includes("Probability Panel") ? 1.4 :
                    methodology.includes("Online")            ? 0.6 :
                    1.0;

                const pollster = row.pollster;
                if (!pollsterCache.has(pollster)) {
                    const r = findPollsterRating(pollster, ratingsMap);
                    pollsterCache.set(pollster, {
                        ppmMultiplier: r ? Math.exp(-r.ppm * 0.5) : 0.75,
                        bias:          r?.bias ?? 0,
                    });
                }
                const { ppmMultiplier, bias } = pollsterCache.get(pollster);

                const endDate = new Date(row.end_date);
                const region  = getRegionFromRow(row);
                poll = polls[key] = {
                    poll_id:      row.poll_id,
                    question_id:  row.question_id,
                    [regionKey]:  region,
                    state:        row.state,
                    pollster,
                    start_date:   row.start_date,
                    end_date:     row.end_date,
                    sample_size:  row.sample_size,
                    sponsorParty: normalizeParty(row.partisan),
                    pollsterBias: bias,
                    weight: Math.sqrt(row.sample_size / 2 || 250) *
                            Math.exp(-(now - endDate) / 86400000 / 30) *
                            methodologyMultiplier *
                            ppmMultiplier,
                    responses: [],
                    _rows: [], 
                };
            }
            poll.responses.push({
                candidate: row.candidate_name,
                party:     normalizeParty(row.party),
                pct:       row.pct,
            });
            poll._rows.push(row); 
        }
        return Object.values(polls);
    }

    function applyCandidateThreshold(polls) {
        const counts = Object.create(null);
        for (const poll of polls) {
            const region = poll[regionKey];
            const seen = new Set();
            counts[region] ??= Object.create(null);
            for (const r of poll.responses) {
                if (excludeRe.test(r.candidate) || seen.has(r.candidate)) continue;
                seen.add(r.candidate);
                counts[region][r.candidate] = (counts[region][r.candidate] || 0) + 1;
            }
        }
        for (const poll of polls) {
            const allowed = counts[poll[regionKey]];
            poll.responses = poll.responses.filter(r =>
                !excludeRe.test(r.candidate) && (allowed[r.candidate] || 0) >= minPolls
            );
        }
        return polls;
    }

    function groupPollsByRegion(polls) {
        const byRegion = Object.create(null);
        for (const p of polls) (byRegion[p[regionKey]] ??= []).push(p);
        return Object.entries(byRegion).map(([region, ps]) => ({ [regionKey]: region, polls: ps }));
    }

    function filterPolls(polls) {
        const filtered = polls.filter(poll => {
            if (poll.responses.length < 2) return false; 
            for (const r of poll.responses) {
                r._candidateLC ??= r.candidate.toLowerCase();
                if (r._candidateLC.includes("generic")) return false;
            }
            const required = primaryWinners[poll[regionKey]];
            if (required) {
                const requiredLast = getLastName(required);
                if (!poll.responses.some(r => getLastName(r.candidate) === requiredLast)) return false;
            }
            return true;
        });
        const counts = Object.create(null);
        for (const p of filtered) counts[p[regionKey]] = (counts[p[regionKey]] || 0) + 1;
        return filtered.filter(p => counts[p[regionKey]] >= 2);
    }

    function computeEstimates(pollsByRegion) {
        const results = Object.create(null);
        for (const entry of pollsByRegion) {
            const region = entry[regionKey];
            const polls  = entry.polls;
            const totals  = Object.create(null);
            const weights = Object.create(null);
            const parties = Object.create(null);

            for (const poll of polls) {
                for (const r of normalizeResponses(poll)) {
                    const c = r.candidate;
                    totals[c]  ??= 0;
                    weights[c] ??= 0;
                    parties[c] = fixKnownIndependents(region, c) || normalizeParty(r.party);
                    totals[c]  += r.pct * poll.weight;
                    weights[c] += poll.weight;
                }
            }

            const out = Object.create(null);
            for (const c in totals) {
                out[c] = { pct: totals[c] / weights[c], party: parties[c] };
            }
            results[region] = renormalizeEstimates(out);
        }
        return results;
    }

    function applyPviToEstimates(region, estimates, nEff) {
        const pvi = pviMap[region] != null ? pviMap[region] + pviOffset : 0;
        const strength = 0.2 * Math.min(2, 5 / Math.sqrt(nEff || 1));
        const out = Object.create(null);
        for (const c in estimates) {
            const { pct: base, party } = estimates[c];
            const shift = party === "DEM" || party === "WFP" ? -pvi * strength
                        : party === "REP"                    ?  pvi * strength : 0;
            out[c] = { pct: base + shift, party };
        }
        return out;
    }

    function computeOutcomes(estimates, pollsByRegion, marketPriors) {
        const pollMap = Object.fromEntries(pollsByRegion.map(p => [p[regionKey], p.polls]));
        const outcomes = Object.create(null);

        for (const region in estimates) {
            const polls  = pollMap[region] || [];
            let nEff = 0;
            for (const p of polls) nEff += p.weight;
            const sigma = nEff <= 0 ? 5 : Math.max(7, 10 / Math.sqrt(nEff));

            const pviAdjusted    = renormalizeEstimates(applyPviToEstimates(region, estimates[region], nEff));
            const marketAdjusted = applyMarketPriorToEstimates(region, pviAdjusted, marketPriors);

            let finalEstimates      = marketAdjusted;
            let rcvEliminationOrder = [];

            if (rcvRegionsSet.has(region) && Object.keys(marketAdjusted).length > 2) {
                let current = Object.assign(Object.create(null), marketAdjusted);
                let currentSize = Object.keys(marketAdjusted).length;
                while (currentSize > 2) {
                    const sortedByVote = Object.entries(current).sort((a, b) => a[1].pct - b[1].pct);
                    const [elimName, elimData] = sortedByVote[0];
                    const elimPct   = elimData.pct;
                    const elimParty = elimData.party;
                    const remaining = sortedByVote.slice(1);

                    let sameWeight = 0, otherWeight = 0;
                    for (const [, d] of remaining) {
                        if (d.party === elimParty) sameWeight  += d.pct;
                        else                       otherWeight += d.pct;
                    }
                    const partyShare = sameWeight > 0 ? 0.8 : 0;
                    const otherShare = 1 - partyShare;

                    const next = Object.create(null);
                    for (const [name, data] of remaining) {
                        let bonus = 0;
                        if (data.party === elimParty && sameWeight > 0)
                            bonus = (data.pct / sameWeight) * elimPct * partyShare;
                        else if (data.party !== elimParty && otherWeight > 0)
                            bonus = (data.pct / otherWeight) * elimPct * otherShare;
                        next[name] = { pct: data.pct + bonus, party: data.party };
                    }
                    rcvEliminationOrder.push(elimName);
                    current = renormalizeEstimates(next);
                    currentSize--;
                }
                finalEstimates = current;
            }

            if (Object.keys(finalEstimates).length === 0) continue;

            const candidatePct   = Object.create(null);
            const candidateParty = Object.create(null);
            for (const c in finalEstimates) {
                candidatePct[c]   = finalEstimates[c].pct;
                candidateParty[c] = finalEstimates[c].party;
            }

            let top1 = -Infinity, top2 = -Infinity;
            for (const c in finalEstimates) {
                const pct = finalEstimates[c].pct;
                if (pct > top1) { top2 = top1; top1 = pct; }
                else if (pct > top2) top2 = pct;
            }
            const margin = top2 === -Infinity ? 0 : top1 - top2;

            const winProbs = monteCarloMulti(candidatePct, sigma);
            const winProbEntries = Object.entries(winProbs)
                .map(([c, p]) => [c, { pct: p, party: candidateParty[c] }])
                .sort((a, b) => b[1].pct - a[1].pct);

            const voteEntries = Object.entries(marketAdjusted).sort((a, b) => b[1].pct - a[1].pct);

            outcomes[region] = {
                _rcvFinalEstimates:      rcvEliminationOrder.length ? finalEstimates : null,
                _rcvEliminationOrder:    rcvEliminationOrder,
                _sortedWinProbabilities: winProbEntries,
                _sortedVoteEstimates:    voteEntries,
                margin,
            };
        }
        return outcomes;
    }

    if (ratingsUrl && !_ratingsPromiseCache[ratingsUrl]) {
        try {
            const localPath = resolve(__dirname, ratingsUrl.replace(/^\.\//, ""));
            const text = readFileSync(localPath, "utf8");
            _ratingsPromiseCache[ratingsUrl] = Promise.resolve(buildRatingsMap(text));
        } catch {
            _ratingsPromiseCache[ratingsUrl] = fetch(ratingsUrl)
                .then(r => r.text())
                .then(buildRatingsMap);
        }
    }

    const [response, marketPrior, ratingsMap] = await Promise.all([
        fetch(url),
        getPolymarketPriors(),
        ratingsUrl ? _ratingsPromiseCache[ratingsUrl] : Promise.resolve(new Map()),
    ]);

    const csvText = await response.text();
    const cutoffDate = new Date("2025-11-11");
    const parsed = Papa.parse(csvText, { header: true, dynamicTyping: true });
    const rows = parsed.data.filter(r =>
        r && r.stage === "general" &&
        r.state &&
        !notGenYetSet.has(getRegionFromRow(r)) &&
        new Date(r.created_at) >= cutoffDate &&
        (!extraRowFilter || extraRowFilter(r))
    );
    const polls      = groupByPollId(rows, ratingsMap);
    const thresholded = applyCandidateThreshold(polls);
    const filtered   = filterPolls(thresholded);
    for (const poll of filtered) {
        for (const r of poll.responses) {
            if (!excludeRe.test(r.candidate) &&
                !someoneElseRe.test(r.candidate) &&
                r.party !== "DEM" && r.party !== "REP") {
                regionsWithNamed3p.add(poll[regionKey]);
                break;
            }
        }
    }
    const byRegion   = groupPollsByRegion(filtered);
    const estimates  = computeEstimates(byRegion);
    return {
        outcomes: { ...defaults, ...computeOutcomes(estimates, byRegion, marketPrior) },
        filteredPolls: filtered, 
    };
}

let _polymarketPromise = null;

async function getPolymarketPriors() {
    if (!_polymarketPromise) {
        _polymarketPromise = (async () => {
            try {
                const res  = await fetch("https://gamma-api.polymarket.com/events/32224");
                const data = await res.json();
                const markets = data.markets;
                if (!markets?.length) return null;

                function parsePrice(market) {
                    try { return parseFloat(JSON.parse(market.outcomePrices)?.[0]); }
                    catch { return parseFloat(market.bestAsk); }
                }
                const demRaw = parsePrice(markets[0]);
                const repRaw = parsePrice(markets[1]);
                if (isNaN(demRaw) || isNaN(repRaw)) return null;
                const sum = demRaw + repRaw;
                return { DEM: (demRaw / sum) * 100, REP: (repRaw / sum) * 100 };
            } catch (err) {
                console.warn("Polymarket fetch failed:", err.message);
                return null;
            }
        })();
    }
    return _polymarketPromise;
}

function applyMarketPriorToEstimates(state, estimates, marketPrior) {
    if (!marketPrior) return estimates;
    const out = Object.create(null);
    for (const candidate in estimates) {
        const { pct, party } = estimates[candidate];
        const marketTarget = marketPrior[party];
        out[candidate] = {
            pct: marketTarget !== undefined ? (1 - 0.06) * pct + 0.06 * marketTarget : pct,
            party,
        };
    }
    return renormalizeEstimates(out);
}

const senateDefaults = {
    "WY": { _isDefault: true, _sortedWinProbabilities: [["Harriet Hageman",   { pct: 1,    party: "REP" }]], _sortedVoteEstimates: [["Harriet Hageman",   { pct: 75, party: "REP" }]] },
    "OR": { _isDefault: true, _sortedWinProbabilities: [["Jeff Merkley",      { pct: 0.95, party: "DEM" }]], _sortedVoteEstimates: [["Jeff Merkley",      { pct: 57, party: "DEM" }]] },
    "ID": { _isDefault: true, _sortedWinProbabilities: [["Jim Risch",         { pct: 1,    party: "REP" }]], _sortedVoteEstimates: [["Jim Risch",         { pct: 62, party: "REP" }]] },
    "CO": { _isDefault: true, _sortedWinProbabilities: [["John Hickenlooper", { pct: 0.92, party: "DEM" }]], _sortedVoteEstimates: [["John Hickenlooper", { pct: 56, party: "DEM" }]] },
    "NM": { _isDefault: true, _sortedWinProbabilities: [["Ben Ray Luján",     { pct: 0.90, party: "DEM" }]], _sortedVoteEstimates: [["Ben Ray Luján",     { pct: 56, party: "DEM" }]] },
    "SD": { _isDefault: true, _sortedWinProbabilities: [["Mike Rounds",       { pct: 1,    party: "REP" }]], _sortedVoteEstimates: [["Mike Rounds",       { pct: 69, party: "REP" }]] },
    "OK": { _isDefault: true, _sortedWinProbabilities: [["Kevin Hern",        { pct: 1,    party: "REP" }]], _sortedVoteEstimates: [["Kevin Hern",        { pct: 64, party: "REP" }]] },
    "IL": { _isDefault: true, _sortedWinProbabilities: [["Juliana Stratton",  { pct: 0.96, party: "DEM" }]], _sortedVoteEstimates: [["Juliana Stratton",  { pct: 58, party: "DEM" }]] },
    "AR": { _isDefault: true, _sortedWinProbabilities: [["Tom Cotton",        { pct: 1,    party: "REP" }]], _sortedVoteEstimates: [["Tom Cotton",        { pct: 66, party: "REP" }]] },
    "LA": { _isDefault: true, _sortedWinProbabilities: [["Republican",        { pct: 0.98, party: "REP" }]], _sortedVoteEstimates: [["Republican",        { pct: 62, party: "REP" }]] },
    "MS": { _isDefault: true, _sortedWinProbabilities: [["Cindy Hyde-Smith",  { pct: 0.9,  party: "REP" }]], _sortedVoteEstimates: [["Cindy Hyde-Smith",  { pct: 56, party: "REP" }]] },
    "KY": { _isDefault: true, _sortedWinProbabilities: [["Andy Barr",         { pct: 0.94, party: "REP" }]], _sortedVoteEstimates: [["Andy Barr",         { pct: 60, party: "REP" }]] },
    "TN": { _isDefault: true, _sortedWinProbabilities: [["Bill Hagerty",      { pct: 1,    party: "REP" }]], _sortedVoteEstimates: [["Bill Hagerty",      { pct: 64, party: "REP" }]] },
    "AL": { _isDefault: true, _sortedWinProbabilities: [["Republican",        { pct: 0.98, party: "REP" }]], _sortedVoteEstimates: [["Republican",        { pct: 62, party: "REP" }]] },
    "WV": { _isDefault: true, _sortedWinProbabilities: [["Shelley Moore Capito", { pct: 1, party: "REP" }]], _sortedVoteEstimates: [["Shelley Moore Capito", { pct: 70, party: "REP" }]] },
    "VA": { _isDefault: true, _sortedWinProbabilities: [["Mark Warner",       { pct: 0.9,  party: "DEM" }]], _sortedVoteEstimates: [["Mark Warner",       { pct: 56, party: "DEM" }]] },
    "NJ": { _isDefault: true, _sortedWinProbabilities: [["Cory Booker",       { pct: 0.95, party: "DEM" }]], _sortedVoteEstimates: [["Cory Booker",       { pct: 57, party: "DEM" }]] },
    "DE": { _isDefault: true, _sortedWinProbabilities: [["Chris Coons",       { pct: 0.97, party: "DEM" }]], _sortedVoteEstimates: [["Chris Coons",       { pct: 58, party: "DEM" }]] },
    "RI": { _isDefault: true, _sortedWinProbabilities: [["Jack Reed",         { pct: 0.99, party: "DEM" }]], _sortedVoteEstimates: [["Jack Reed",         { pct: 64, party: "DEM" }]] },
};

const govDefaults = {
    "WY": { _isDefault: true, _sortedWinProbabilities: [["Megan Degenfelder",    { pct: 1,    party: "REP" }]], _sortedVoteEstimates: [["Megan Degenfelder",    { pct: 70, party: "REP" }]] },
    "CA": { _isDefault: true, _sortedWinProbabilities: [["Democrat",             { pct: 0.95, party: "DEM" }]], _sortedVoteEstimates: [["Democrat",             { pct: 57, party: "DEM" }]] },
    "ID": { _isDefault: true, _sortedWinProbabilities: [["Brad Little",          { pct: 1,    party: "REP" }]], _sortedVoteEstimates: [["Brad Little",          { pct: 62, party: "REP" }]] },
    "CO": { _isDefault: true, _sortedWinProbabilities: [["Democrat",             { pct: 0.92, party: "DEM" }]], _sortedVoteEstimates: [["Democrat",             { pct: 56, party: "DEM" }]] },
    "NM": { _isDefault: true, _sortedWinProbabilities: [["Democrat",             { pct: 0.90, party: "DEM" }]], _sortedVoteEstimates: [["Democrat",             { pct: 56, party: "DEM" }]] },
    "SD": { _isDefault: true, _sortedWinProbabilities: [["Republican",           { pct: 1,    party: "REP" }]], _sortedVoteEstimates: [["Republican",           { pct: 63, party: "REP" }]] },
    "OK": { _isDefault: true, _sortedWinProbabilities: [["Republican",           { pct: 0.9,  party: "REP" }]], _sortedVoteEstimates: [["Republican",           { pct: 56, party: "REP" }]] },
    "IL": { _isDefault: true, _sortedWinProbabilities: [["JB Pritzker",          { pct: 0.96, party: "DEM" }]], _sortedVoteEstimates: [["JB Pritzker",          { pct: 58, party: "DEM" }]] },
    "AR": { _isDefault: true, _sortedWinProbabilities: [["Sarah Huckabee Sanders", { pct: 1,  party: "REP" }]], _sortedVoteEstimates: [["Sarah Huckabee Sanders", { pct: 64, party: "REP" }]] },
    "KS": { _isDefault: true, _sortedWinProbabilities: [["Republican",           { pct: 0.75, party: "REP" }]], _sortedVoteEstimates: [["Republican",           { pct: 55, party: "REP" }]] },
    "NE": { _isDefault: true, _sortedWinProbabilities: [["Jim Pillen",           { pct: 0.93, party: "REP" }]], _sortedVoteEstimates: [["Jim Pillen",           { pct: 59, party: "REP" }]] },
    "GA": { _isDefault: true, _sortedWinProbabilities: [["Keisha Lance Bottoms", { pct: 0.56, party: "DEM" }]], _sortedVoteEstimates: [["Keisha Lance Bottoms", { pct: 51, party: "DEM" }]] },
    "TN": { _isDefault: true, _sortedWinProbabilities: [["Marsha Blackburn",     { pct: 1,    party: "REP" }]], _sortedVoteEstimates: [["Marsha Blackburn",     { pct: 64, party: "REP" }]] },
    "AL": { _isDefault: true, _sortedWinProbabilities: [["Tommy Tuberville",     { pct: 0.96, party: "REP" }]], _sortedVoteEstimates: [["Tommy Tuberville",     { pct: 60, party: "REP" }]] },
    "SC": { _isDefault: true, _sortedWinProbabilities: [["Republican",           { pct: 0.9,  party: "REP" }]], _sortedVoteEstimates: [["Republican",           { pct: 55, party: "REP" }]] },
    "VT": { _isDefault: true, _sortedWinProbabilities: [["Phil Scott",           { pct: 1,    party: "REP" }]], _sortedVoteEstimates: [["Phil Scott",           { pct: 73, party: "REP" }]] },
    "CT": { _isDefault: true, _sortedWinProbabilities: [["Democrat",             { pct: 0.91, party: "DEM" }]], _sortedVoteEstimates: [["Democrat",             { pct: 56, party: "DEM" }]] },
    "MD": { _isDefault: true, _sortedWinProbabilities: [["Wes Moore",            { pct: 0.96, party: "DEM" }]], _sortedVoteEstimates: [["Wes Moore",            { pct: 63, party: "DEM" }]] },
    "RI": { _isDefault: true, _sortedWinProbabilities: [["Helena Foulkes",       { pct: 0.90, party: "DEM" }]], _sortedVoteEstimates: [["Helena Foulkes",       { pct: 55, party: "DEM" }]] },
    "WI": { _isDefault: true, _sortedWinProbabilities: [["Democrat",             { pct: 0.73, party: "DEM" }]], _sortedVoteEstimates: [["Democrat",             { pct: 50, party: "DEM" }]] },
    "ME": { _isDefault: true, _sortedWinProbabilities: [["Democrat",             { pct: 0.76, party: "DEM" }]], _sortedVoteEstimates: [["Democrat",             { pct: 51, party: "DEM" }]] },
    "HI": { _isDefault: true, _sortedWinProbabilities: [["Josh Green",           { pct: 0.96, party: "DEM" }]], _sortedVoteEstimates: [["Josh Green",           { pct: 63, party: "DEM" }]] },
    "IA": { _isDefault: true, _sortedWinProbabilities: [["Rob Sand",{ pct: 0.53, party: "DEM" }],["Zach Lahn", { pct: 0.47, party: "REP" }]],   _sortedVoteEstimates: [["Rob Sand", { pct: 50.50, party: "DEM" }],["Zach Lahn", { pct: 49.50, party: "REP" }]] }
};

const _defaultsSrc = readFileSync(resolve(__dirname, "defaults.js"), "utf8");
const _defaultsModule = { exports: {} };
new Function("module", "exports", _defaultsSrc + `
    module.exports = { houseDefaults };
`)(_defaultsModule, _defaultsModule.exports);
const { houseDefaults } = _defaultsModule.exports;

const senateLink = "https://www.nytimes.com/newsgraphics/polls/senate.csv";
const senateNotGenYet = ["US", "MS"];
const primaryWinnersByState = {
    NE: "dan osborn", ME: "graham platner", OH: "sherrod brown",
    SD: "julian beaudion", IA: "josh turek", GA: "mike collins",
    NH: "john sununu", MN: "x flanagan", KS: "x schmidt",
    MA: "x markey", FL: "x vindman", MI: "x el-sayed",
    TX: "x paxton", KY: "x barr",
};
const cookPVI = {
    AL:15, AK:6, AZ:0, AR:15, CA:-9, CO:-6, CT:-8, DE:-8, FL:8, GA:2, HI:-13, ID:18,
    IL:-6, IN:9, IA:6, KS:8, KY:15, LA:11, ME:-4, MD:-15, MA:-10, MI:-3, MN:-7, MS:11,
    MO:9, MT:6, NE:8, NV:1, NH:-2, NJ:0, NM:-7, NY:-8, NC:1, ND:18, OH:3, OK:17, OR:-8,
    PA:1, RI:-8, SC:8, SD:15, TN:14, TX:6, UT:11, VT:-9, VA:-6, WA:-10, WV:21, WI:-2, WY:23,
};
const SENATE_EXCLUDE_RE = /undecided|don't know|daines|ryan|allred|crockett|other|refused|would not vote/i;
const SENATE_NO_ELECTION = ["HI","CA","NV","UT","AZ","WA","ND","MO","WI","IN","PA","NY","MD","VT","CT"];
const senateCurrentParty = { VA:"DEM", AL:"REP", NC:"REP", AK:"REP", MN:"DEM", NH:"DEM", SD:"REP", ID:"REP", NE:"REP", RI:"DEM", NM:"DEM", MI:"DEM", GA:"DEM", WV:"REP", FL:"REP", OR:"DEM", KY:"REP", KS:"REP", MA:"DEM", WY:"REP", OH:"REP", MS:"REP", CO:"DEM", TN:"REP", SC:"REP", IA:"REP", IL:"DEM", MT:"REP", AR:"REP", TX:"REP", DE:"DEM", ME:"REP", LA:"REP", NJ:"DEM", OK:"REP" };

const Link_gov = "https://www.nytimes.com/newsgraphics/polls/governor.csv";
const notGenYet_gov = ["US", "GA", "WI"];
const primaryWinnersByState_gov = {
    RI:"x foulkes", OR:"x drazan", FL:"x donalds", MA:"x minogue", MN:"x lindell",
    NH:"x warmington", NV:"x lombardo", AK:"x wilson", AZ:"x biggs", MI:"x james", WI:"x tiffany",
    CA: "x hilton", IA: "x lahn"
};
const cookPVI_gov = { ...cookPVI }; 
const GOV_EXCLUDE_RE = /undecided|don't know|demings|dixon|porter|steyer|lytle|duggan|stefanik|pizzo|bell|other|refused|would not vote/i;
const GOV_NO_ELECTION = ["WA","UT","MT","ND","MO","LA","MS","KY","IN","WV","VA","NC","DE","NJ"];
const govCurrentParty = { AL:"REP", AK:"REP", AZ:"DEM", AR:"REP", CA:"DEM", CO:"DEM", CT:"DEM", FL:"REP", GA:"REP", HI:"DEM", ID:"REP", IL:"DEM", IA:"REP", KS:"DEM", ME:"DEM", MD:"DEM", MA:"DEM", MI:"DEM", MN:"DEM", NE:"REP", NV:"REP", NH:"REP", NM:"DEM", NY:"DEM", OH:"REP", OK:"REP", OR:"DEM", PA:"DEM", RI:"DEM", SC:"REP", SD:"REP", TN:"REP", TX:"REP", VT:"REP", WI:"DEM", WY:"REP" };

const houseLink = "https://www.nytimes.com/newsgraphics/polls/house.csv";
const houseNotGenYet = ["NM02","TX34","WA03","MI04","AZ06","NC10","NE01","NC14","VA01","WI01","FL28","TX23","MI07","CA40"];
const housePrimaryWinnersByDistrict = { KY06:"ralph alvarado", MI10:"x hines", MT01:"x forstag", ME02:"x baldacci" };
const houseDistrictPVI = { AK01:6, AL01:27, AL02:-5, AL03:23, AL04:33, AL05:15, AL06:20, AL07:-13, AR01:23, AR02:8, AR03:13, AR04:20, AZ01:1, AZ02:7, AZ03:-22, AZ04:-4, AZ05:10, AZ06:0, AZ07:-13, AZ08:8, AZ09:15, CA01:12, CA02:-24, CA03:2, CA04:-17, CA05:8, CA06:-8, CA07:-16, CA08:-24, CA09:-1, CA10:-18, CA11:-36, CA12:-39, CA13:1, CA14:-20, CA15:-26, CA16:-26, CA17:-21, CA18:-17, CA19:-18, CA20:15, CA21:-4, CA22:1, CA23:8, CA24:-13, CA25:-3, CA26:-8, CA27:-3, CA28:-15, CA29:-20, CA30:-22, CA31:-10, CA32:-17, CA33:-7, CA34:-28, CA35:-8, CA36:-21, CA37:-33, CA38:-10, CA39:-7, CA40:1, CA41:2, CA42:-18, CA43:-27, CA44:-19, CA45:-1, CA46:-11, CA47:-3, CA48:7, CA49:-4, CA50:-16, CA51:-13, CA52:-13, CO01:-29, CO02:-20, CO03:5, CO04:9, CO05:5, CO06:-11, CO07:-8, CO08:0, CT01:-12, CT02:-4, CT03:-8, CT04:-13, CT05:-3, DE01:-8, FL01:18, FL02:8, FL03:10, FL04:5, FL05:10, FL06:14, FL07:5, FL08:11, FL09:-4, FL10:-13, FL11:8, FL12:17, FL13:5, FL14:-5, FL15:5, FL16:7, FL17:11, FL18:14, FL19:14, FL20:-22, FL21:7, FL22:-4, FL23:-2, FL24:-18, FL25:-5, FL26:16, FL27:6, FL28:10, GA01:8, GA02:-4, GA03:15, GA04:-27, GA05:-36, GA06:-25, GA07:11, GA08:15, GA09:17, GA10:11, GA11:12, GA12:7, GA13:-21, GA14:19, HI01:-13, HI02:-12, IA01:4, IA02:4, IA03:2, IA04:15, ID01:22, ID02:13, IL01:-18, IL02:-18, IL03:-17, IL04:-17, IL05:-19, IL06:-3, IL07:-34, IL08:-5, IL09:-19, IL10:-12, IL11:-6, IL12:22, IL13:-5, IL14:-3, IL15:20, IL16:11, IL17:-3, IN01:-1, IN02:13, IN03:16, IN04:15, IN05:8, IN06:16, IN07:-21, IN08:18, IN09:15, KS01:16, KS02:10, KS03:-2, KS04:12, KY01:23, KY02:20, KY03:-10, KY04:18, KY05:32, KY06:7, LA01:19, LA02:-17, LA03:22, LA04:26, LA05:18, LA06:-8, MA01:-8, MA02:-13, MA03:-11, MA04:-11, MA05:-24, MA06:-11, MA07:-34, MA08:-15, MA09:-6, MD01:8, MD02:-10, MD03:-12, MD04:-39, MD05:-17, MD06:-3, MD07:-31, MD08:-30, ME01:-11, ME02:4, MI01:11, MI02:15, MI03:-4, MI04:3, MI05:13, MI06:-12, MI07:0, MI08:1, MI09:16, MI10:3, MI11:-9, MI12:-21, MI13:-22, MN01:6, MN02:-3, MN03:-11, MN04:-18, MN05:-32, MN06:10, MN07:18, MN08:7, MO01:-29, MO02:4, MO03:13, MO04:21, MO05:-12, MO06:19, MO07:21, MO08:27, MS01:18, MS02:-11, MS03:14, MS04:21, MT01:5, MT02:15, NC01:3, NC02:-17, NC03:10, NC04:-23, NC05:9, NC06:9, NC07:7, NC08:10, NC09:8, NC10:9, NC11:5, NC12:-24, NC13:8, NC14:8, ND01:18, NE01:6, NE02:-3, NE03:27, NH01:-2, NH02:-2, NJ01:-10, NJ02:5, NJ03:-5, NJ04:14, NJ05:-2, NJ06:-5, NJ07:0, NJ08:-15, NJ09:-2, NJ10:-27, NJ11:-5, NJ12:-13, NM01:-7, NM02:0, NM03:-3, NV01:-2, NV02:7, NV03:-1, NV04:-2, NY01:4, NY02:6, NY03:0, NY04:-2, NY05:-24, NY06:-6, NY07:-25, NY08:-24, NY09:-22, NY10:-32, NY11:10, NY12:-33, NY13:-32, NY14:-19, NY15:-27, NY16:-18, NY17:-1, NY18:-2, NY19:-1, NY20:-8, NY21:10, NY22:-4, NY23:10, NY24:11, NY25:-10, NY26:-11, OH01:-3, OH02:24, OH03:-21, OH04:18, OH05:14, OH06:16, OH07:5, OH08:12, OH09:3, OH10:3, OH11:-28, OH12:16, OH13:0, OH14:9, OH15:4, OK01:11, OK02:28, OK03:23, OK04:17, OK05:9, OR01:-20, OR02:14, OR03:-24, OR04:-6, OR05:-4, OR06:-6, PA01:-1, PA02:-19, PA03:-40, PA04:-8, PA05:-15, PA06:-6, PA07:1, PA08:4, PA09:19, PA10:3, PA11:11, PA12:-10, PA13:23, PA14:17, PA15:19, PA16:11, PA17:-3, RI01:-12, RI02:-4, SC01:6, SC02:7, SC03:21, SC04:11, SC05:11, SC06:-13, SC07:12, SD01:15, TN01:29, TN02:17, TN03:18, TN04:21, TN05:8, TN06:17, TN07:10, TN08:21, TN09:-23, TX01:25, TX02:12, TX03:10, TX04:16, TX05:13, TX06:14, TX07:-12, TX08:16, TX09:-24, TX10:12, TX11:22, TX12:11, TX13:24, TX14:17, TX15:7, TX16:-11, TX17:14, TX18:-21, TX19:25, TX20:-12, TX21:11, TX22:9, TX23:7, TX24:7, TX25:18, TX26:11, TX27:14, TX28:2, TX29:-12, TX30:-25, TX31:11, TX32:-13, TX33:-19, TX34:0, TX35:-19, TX36:18, TX37:-26, TX38:10, UT01:10, UT02:10, UT03:10, UT04:14, VA01:3, VA02:0, VA03:-18, VA04:-17, VA05:6, VA06:12, VA07:-2, VA08:-26, VA09:22, VA10:-6, VA11:-18, VT01:-17, WA01:-15, WA02:-12, WA03:2, WA04:10, WA05:5, WA06:-10, WA07:-39, WA08:-3, WA09:-22, WA10:-9, WI01:2, WI02:-21, WI03:3, WI04:-26, WI05:11, WI06:8, WI07:11, WI08:8, WV01:22, WV02:20, WY01:23 };
const HOUSE_EXCLUDE_RE = /undecided|don't know|dembo|zinke|dotson|other|refused|would not vote/i;
const houseCurrentParty = { "AL01":"REP","AL02":"DEM","AL03":"REP","AL04":"REP","AL05":"REP","AL06":"REP","AL07":"DEM","AK00":"REP","AZ01":"REP","AZ02":"REP","AZ03":"DEM","AZ04":"DEM","AZ05":"REP","AZ06":"REP","AZ07":"DEM","AZ08":"REP","AZ09":"REP","AR01":"REP","AR02":"REP","AR03":"REP","AR04":"REP","CA01":"REP","CA02":"DEM","CA03":"IND","CA04":"DEM","CA05":"REP","CA06":"DEM","CA07":"DEM","CA08":"DEM","CA09":"DEM","CA10":"DEM","CA11":"DEM","CA12":"DEM","CA13":"DEM","CA14":"DEM","CA15":"DEM","CA16":"DEM","CA17":"DEM","CA18":"DEM","CA19":"DEM","CA20":"REP","CA21":"DEM","CA22":"REP","CA23":"REP","CA24":"DEM","CA25":"DEM","CA26":"DEM","CA27":"DEM","CA28":"DEM","CA29":"DEM","CA30":"DEM","CA31":"DEM","CA32":"DEM","CA33":"DEM","CA34":"DEM","CA35":"DEM","CA36":"DEM","CA37":"DEM","CA38":"DEM","CA39":"DEM","CA40":"REP","CA41":"REP","CA42":"DEM","CA43":"DEM","CA44":"DEM","CA45":"DEM","CA46":"DEM","CA47":"DEM","CA48":"REP","CA49":"DEM","CA50":"DEM","CA51":"DEM","CA52":"DEM","CO01":"DEM","CO02":"DEM","CO03":"REP","CO04":"REP","CO05":"REP","CO06":"DEM","CO07":"DEM","CO08":"REP","CT01":"DEM","CT02":"DEM","CT03":"DEM","CT04":"DEM","CT05":"DEM","DE00":"DEM","FL01":"REP","FL02":"REP","FL03":"REP","FL04":"REP","FL05":"REP","FL06":"REP","FL07":"REP","FL08":"REP","FL09":"DEM","FL10":"DEM","FL11":"REP","FL12":"REP","FL13":"REP","FL14":"DEM","FL15":"REP","FL16":"REP","FL17":"REP","FL18":"REP","FL19":"REP","FL20":"DEM","FL21":"REP","FL22":"DEM","FL23":"DEM","FL24":"DEM","FL25":"DEM","FL26":"REP","FL27":"REP","FL28":"REP","GA01":"REP","GA02":"DEM","GA03":"REP","GA04":"DEM","GA05":"DEM","GA06":"DEM","GA07":"REP","GA08":"REP","GA09":"REP","GA10":"REP","GA11":"REP","GA12":"REP","GA13":"DEM","GA14":"REP","HI01":"DEM","HI02":"DEM","ID01":"REP","ID02":"REP","IL01":"DEM","IL02":"DEM","IL03":"DEM","IL04":"DEM","IL05":"DEM","IL06":"DEM","IL07":"DEM","IL08":"DEM","IL09":"DEM","IL10":"DEM","IL11":"DEM","IL12":"REP","IL13":"DEM","IL14":"DEM","IL15":"REP","IL16":"REP","IL17":"DEM","IN01":"DEM","IN02":"REP","IN03":"REP","IN04":"REP","IN05":"REP","IN06":"REP","IN07":"DEM","IN08":"REP","IN09":"REP","IA01":"REP","IA02":"REP","IA03":"REP","IA04":"REP","KS01":"REP","KS02":"REP","KS03":"DEM","KS04":"REP","KY01":"REP","KY02":"REP","KY03":"DEM","KY04":"REP","KY05":"REP","KY06":"REP","LA01":"REP","LA02":"DEM","LA03":"REP","LA04":"REP","LA05":"REP","LA06":"DEM","ME01":"DEM","ME02":"DEM","MD01":"REP","MD02":"DEM","MD03":"DEM","MD04":"DEM","MD05":"DEM","MD06":"DEM","MD07":"DEM","MD08":"DEM","MA01":"DEM","MA02":"DEM","MA03":"DEM","MA04":"DEM","MA05":"DEM","MA06":"DEM","MA07":"DEM","MA08":"DEM","MA09":"DEM","MI01":"REP","MI02":"REP","MI03":"DEM","MI04":"REP","MI05":"REP","MI06":"DEM","MI07":"REP","MI08":"DEM","MI09":"REP","MI10":"REP","MI11":"DEM","MI12":"DEM","MI13":"DEM","MN01":"REP","MN02":"DEM","MN03":"DEM","MN04":"DEM","MN05":"DEM","MN06":"REP","MN07":"REP","MN08":"REP","MS01":"REP","MS02":"DEM","MS03":"REP","MS04":"REP","MO01":"DEM","MO02":"REP","MO03":"REP","MO04":"REP","MO05":"DEM","MO06":"REP","MO07":"REP","MO08":"REP","MT01":"REP","MT02":"REP","NE01":"REP","NE02":"REP","NE03":"REP","NV01":"DEM","NV02":"REP","NV03":"DEM","NV04":"DEM","NH01":"DEM","NH02":"DEM","NJ01":"DEM","NJ02":"REP","NJ03":"DEM","NJ04":"REP","NJ05":"DEM","NJ06":"DEM","NJ07":"REP","NJ08":"DEM","NJ09":"DEM","NJ10":"DEM","NJ11":"DEM","NJ12":"DEM","NM01":"DEM","NM02":"DEM","NM03":"DEM","NY01":"REP","NY02":"REP","NY03":"DEM","NY04":"DEM","NY05":"DEM","NY06":"DEM","NY07":"DEM","NY08":"DEM","NY09":"DEM","NY10":"DEM","NY11":"REP","NY12":"DEM","NY13":"DEM","NY14":"DEM","NY15":"DEM","NY16":"DEM","NY17":"REP","NY18":"DEM","NY19":"DEM","NY20":"DEM","NY21":"REP","NY22":"DEM","NY23":"REP","NY24":"REP","NY25":"DEM","NY26":"DEM","NC01":"DEM","NC02":"DEM","NC03":"REP","NC04":"DEM","NC05":"REP","NC06":"REP","NC07":"REP","NC08":"REP","NC09":"REP","NC10":"REP","NC11":"REP","NC12":"DEM","NC13":"REP","NC14":"REP","ND00":"REP","OH01":"DEM","OH02":"REP","OH03":"DEM","OH04":"REP","OH05":"REP","OH06":"REP","OH07":"REP","OH08":"REP","OH09":"DEM","OH10":"REP","OH11":"DEM","OH12":"REP","OH13":"DEM","OH14":"REP","OH15":"REP","OK01":"REP","OK02":"REP","OK03":"REP","OK04":"REP","OK05":"REP","OR01":"DEM","OR02":"REP","OR03":"DEM","OR04":"DEM","OR05":"DEM","OR06":"DEM","PA01":"REP","PA02":"DEM","PA03":"DEM","PA04":"DEM","PA05":"DEM","PA06":"DEM","PA07":"REP","PA08":"REP","PA09":"REP","PA10":"REP","PA11":"REP","PA12":"DEM","PA13":"REP","PA14":"REP","PA15":"REP","PA16":"REP","PA17":"DEM","RI01":"DEM","RI02":"DEM","SC01":"REP","SC02":"REP","SC03":"REP","SC04":"REP","SC05":"REP","SC06":"DEM","SC07":"REP","SD00":"REP","TN01":"REP","TN02":"REP","TN03":"REP","TN04":"REP","TN05":"REP","TN06":"REP","TN07":"REP","TN08":"REP","TN09":"DEM","TX01":"REP","TX02":"REP","TX03":"REP","TX04":"REP","TX05":"REP","TX06":"REP","TX07":"DEM","TX08":"REP","TX09":"DEM","TX10":"REP","TX11":"REP","TX12":"REP","TX13":"REP","TX14":"REP","TX15":"REP","TX16":"DEM","TX17":"REP","TX18":"DEM","TX19":"REP","TX20":"DEM","TX21":"REP","TX22":"REP","TX23":"REP","TX24":"REP","TX25":"REP","TX26":"REP","TX27":"REP","TX28":"DEM","TX29":"DEM","TX30":"DEM","TX31":"REP","TX32":"DEM","TX33":"DEM","TX34":"DEM","TX35":"DEM","TX36":"REP","TX37":"DEM","TX38":"REP","UT01":"REP","UT02":"REP","UT03":"REP","UT04":"REP","VT00":"DEM","VA01":"REP","VA02":"REP","VA03":"DEM","VA04":"DEM","VA05":"REP","VA06":"REP","VA07":"DEM","VA08":"DEM","VA09":"REP","VA10":"DEM","VA11":"DEM","WA01":"DEM","WA02":"DEM","WA03":"DEM","WA04":"REP","WA05":"REP","WA06":"DEM","WA07":"DEM","WA08":"DEM","WA09":"DEM","WA10":"DEM","WV01":"REP","WV02":"REP","WI01":"REP","WI02":"DEM","WI03":"REP","WI04":"DEM","WI05":"REP","WI06":"REP","WI07":"REP","WI08":"REP","WY00":"REP" };

function houseDistrictCode(row) {
    return row.seat_number < 10
        ? `${row.state}0${row.seat_number}`
        : `${row.state}${row.seat_number}`;
}

const _atLargeStates = new Set(["AK", "VT", "WY", "ND", "SD", "DE"]);
function houseMapDistrictCode(district) {
    if (district.endsWith("01") && _atLargeStates.has(district.slice(0, 2)))
        return district.slice(0, 2) + "00";
    return district;
}

function computeRating(p) {
    return p >= 0.95 ? "solid" : p >= 0.8 ? "likely" : p >= 0.65 ? "lean" : "tilt";
}

/**
 * @param {string}   region      
 * @param {object}   outcome        
 * @param {object}   currentParty  
 * @param {string[]} rcvRegions    
 * @param {string}   [mapRegion]    
 * @param {object}   [currentPartyForDisplay] 
 */

function buildRegionEntry(region, outcome, currentParty, rcvRegions, mapRegion, currentPartyForDisplay) {
    mapRegion ??= region;
    currentPartyForDisplay ??= currentParty;

    const [[winner, winnerData]] = outcome._sortedWinProbabilities;
    const winnerParty = winnerData.party;
    const p = winnerData.pct;
    const rating    = computeRating(p);
    const ratingKey = rating + winnerParty[0];

    const prevParty = currentParty[region];
    const isFlip    = !!(prevParty && winnerParty !== prevParty);
    const prevPartyDisplay = currentPartyForDisplay[mapRegion];
    const isDefault = outcome._isDefault ?? false;

    const nameOps = [];
    if (isFlip) {
        if (isDefault) nameOps.push({ op: "append", value: "<br>" });
        nameOps.push({ op: "append", value: ` (FLIP ${prevPartyDisplay} → ${winnerParty})` });
        nameOps.push({ op: "color",  value: colorMapping["likely" + winnerParty[0]] });
    }
    if (isDefault) {
        nameOps.push({ op: "append", value: "* (default values)" });
        nameOps.push({ op: "color",  value: "#FF0000" });
    }

    const isRcvRegion = rcvRegions.includes(region);
    let description = "<b>Win Probability:</b><br>";
    for (const [name, { pct }] of outcome._sortedWinProbabilities) {
        if ((pct * 100).toFixed(2) !== "0.00")
            description += `${name}: ${(pct * 100).toFixed(2)}%<br>`;
    }
    description += isRcvRegion
        ? "<b>Vote Estimate (first round):</b><br>"
        : "<b>Vote Estimate:</b><br>";
    for (const [name, { pct }] of outcome._sortedVoteEstimates) {
        if (pct.toFixed(2) !== "0.00")
            description += `${name}: ${pct.toFixed(2)}%<br>`;
    }
    if (outcome._rcvFinalEstimates) {
        description += "<b>Vote Estimate (final round):</b><br>";
        const finalSorted = Object.entries(outcome._rcvFinalEstimates).sort((a, b) => b[1].pct - a[1].pct);
        for (const [name, { pct }] of finalSorted)
            description += `${name}: ${pct.toFixed(2)}%<br>`;
        if (outcome._rcvEliminationOrder.length)
            description += `<i>Eliminated: ${outcome._rcvEliminationOrder.join(" → ")}</i><br>`;
    }

    return {
        color: ratingKey,
        nameOps,
        description,
        pulse: isFlip,
        noElection: false,
        isDefault,
        isFlip,
        prevParty: prevPartyDisplay ?? null,
        winner,
        winnerParty,
        winProbability: p,
        rating,
    };
}

function blankSeats() {
    return {
        DEM: 0, REP: 0, IND: 0, UNK: 0,
        solidR: 0, likelyR: 0, leanR: 0, tiltR: 0,
        tiltD: 0, leanD: 0, likelyD: 0, solidD: 0,
        tiltI: 0, leanI: 0, likelyI: 0, solidI: 0,
        tiltL: 0, leanL: 0, likelyL: 0, solidL: 0,
    };
}

function subtractSeats(seats, total) {
    const ratingKeys = ["solidD","likelyD","leanD","tiltD","solidR","likelyR","leanR","tiltR","solidI","likelyI","leanI","tiltI","solidL","likelyL","leanL","tiltL"];
    let sum = seats.DEM + seats.REP + seats.IND;
    for (const k of ratingKeys) sum += seats[k];
    seats.UNK = total - sum;
    return seats;
}

async function buildSenate() {
    console.log("  fetching senate...");
    const { outcomes, filteredPolls } = await runRacePipeline(senateLink, {
        excludeRe:            SENATE_EXCLUDE_RE,
        primaryWinners:       primaryWinnersByState,
        pviMap:               cookPVI,
        notGenYet:            senateNotGenYet,
        fixKnownIndependents: (state, name) =>
            state === "NE" && name?.toLowerCase().includes("osborn") ? "IND" : null,
        getRegionFromRow:     row => row.state,
        regionKey:            "state",
        defaults:             senateDefaults,
        extraRowFilter:       row => row.display_name !== "Praecones Analytica",
        currentParty:         senateCurrentParty,
        ratingsUrl:           "./data-GiFps.csv",
        rcvRegions:           ["AK", "ME"],
        excludeQuestionIds: ["4e57a172-4867-4b0c-a8ff-534bcf7ad2b3", "12e20038-9490-49cb-987c-808f22073a71", "8641969d-bfcf-4367-93b8-d7ae2d45694b"],
    });

    const seats  = { ...blankSeats(), DEM: 32, REP: 31, IND: 2 };
    const gains  = { DEM: 0, REP: 0, IND: 0 };
    const losses = { DEM: 0, REP: 0, IND: 0 };
    const regions = {};

    for (const state in outcomes) {
        const entry = buildRegionEntry(state, outcomes[state], senateCurrentParty, ["AK", "ME"]);
        regions[state] = entry;
        seats[entry.color] = (seats[entry.color] || 0) + 1;
        if (entry.isFlip) {
            gains[entry.winnerParty]++;
            losses[senateCurrentParty[state]]++;
        }
    }
    for (const state of SENATE_NO_ELECTION) {
        regions[state] = { color: "noElec", description: "No election", nameOps: [], pulse: false, noElection: true };
    }

    subtractSeats(seats, 100);

    const seatD = seats.solidD + seats.likelyD + seats.leanD + seats.tiltD;
    const seatR = seats.solidR + seats.likelyR + seats.leanR + seats.tiltR;
    const seatI = seats.solidI + seats.likelyI + seats.leanI + seats.tiltI;
    const summaryHTML = `
        <span style="color:#577ccc"><b>D: ${seatD + seats.DEM}</b>  ${netStr(gains, losses, "DEM", "#577ccc")}</span>
        ${seatI ? `<span style="color:#8e20c7"><b>+ ${seatI + seats.IND} I</b> ${netStr(gains, losses, "IND", "#8e20c7")}</span>` : ""}
        &nbsp;|&nbsp;
        <span style="color:#d22532"><b>R: ${seatR + seats.REP}</b>  ${netStr(gains, losses, "REP", "#d22532")}</span>
    `;

    return { regions, seats, summaryHTML, filteredPolls };
}

async function buildGov() {
    console.log("  fetching governors...");
    const { outcomes, filteredPolls } = await runRacePipeline(Link_gov, {
        excludeRe:            GOV_EXCLUDE_RE,
        primaryWinners:       primaryWinnersByState_gov,
        pviMap:               cookPVI_gov,
        notGenYet:            notGenYet_gov,
        fixKnownIndependents: (state, name) =>
            state === "MN" && name?.toLowerCase().includes("klobuchar") ? "DEM" : null,
        getRegionFromRow:     row => row.state,
        regionKey:            "state",
        defaults:             govDefaults,
        ratingsUrl:           "./data-GiFps.csv",
        currentParty:         govCurrentParty,
        rcvRegions:           ["AK"],
    });

    const seats  = { ...blankSeats(), DEM: 6, REP: 8, IND: 0 };
    const gains  = { DEM: 0, REP: 0, IND: 0 };
    const losses = { DEM: 0, REP: 0, IND: 0 };
    const regions = {};

    for (const state in outcomes) {
        const entry = buildRegionEntry(state, outcomes[state], govCurrentParty, ["AK"]);
        regions[state] = entry;
        seats[entry.color] = (seats[entry.color] || 0) + 1;
        if (entry.isFlip) {
            gains[entry.winnerParty]++;
            losses[govCurrentParty[state]]++;
        }
    }
    for (const state of GOV_NO_ELECTION) {
        regions[state] = { color: "noElec", description: "No election", nameOps: [], pulse: false, noElection: true };
    }

    subtractSeats(seats, 50);

    const seatD = seats.solidD + seats.likelyD + seats.leanD + seats.tiltD;
    const seatR = seats.solidR + seats.likelyR + seats.leanR + seats.tiltR;
    const seatI = seats.solidI + seats.likelyI + seats.leanI + seats.tiltI;
    const summaryHTML = `
        <span style="color:#577ccc"><b>D: ${seatD + seats.DEM}</b>  ${netStr(gains, losses, "DEM", "#577ccc")}</span>
        ${seatI ? `&nbsp;|&nbsp; <span style="color:#8e20c7"><b>+ ${seatI + seats.IND} I (caucus D)</b> ${netStr(gains, losses, "IND", "#8e20c7")}</span>` : ""}
        &nbsp;|&nbsp;
        <span style="color:#d22532"><b>R: ${seatR + seats.REP}</b>  ${netStr(gains, losses, "REP", "#d22532")}</span>
    `;

    return { regions, seats, summaryHTML, filteredPolls };
}

async function buildHouse() {
    console.log("  fetching house...");
    const { outcomes, filteredPolls } = await runRacePipeline(houseLink, {
        excludeRe:            HOUSE_EXCLUDE_RE,
        primaryWinners:       housePrimaryWinnersByDistrict,
        pviMap:               houseDistrictPVI,
        notGenYet:            houseNotGenYet,
        fixKnownIndependents: () => null,
        getRegionFromRow:     row => houseDistrictCode(row),
        regionKey:            "district",
        defaults:             houseDefaults,
        currentParty:         houseCurrentParty,
        rcvRegions:           ["AK01", "ME01", "ME02"],
        ratingsUrl:           "./data-GiFps.csv",
        extraRowFilter:       row => row.seat_number != null,
    });

    const seats  = blankSeats();
    const gains  = { DEM: 0, REP: 0, IND: 0 };
    const losses = { DEM: 0, REP: 0, IND: 0 };
    const regions = {};

    for (const district in outcomes) {
        const mapDistrict = houseMapDistrictCode(district);
        const entry = buildRegionEntry(
            district, outcomes[district],
            houseCurrentParty,        
            ["AK00", "ME01", "ME02"],
            mapDistrict,         
            houseCurrentParty,        
        );
        regions[mapDistrict] = entry;
        seats[entry.color] = (seats[entry.color] || 0) + 1;
        if (entry.isFlip) {
            gains[entry.winnerParty]++;
            losses[houseCurrentParty[mapDistrict]]++;
        }
    }

    subtractSeats(seats, 435);

    const seatD = seats.solidD + seats.likelyD + seats.leanD + seats.tiltD;
    const seatR = seats.solidR + seats.likelyR + seats.leanR + seats.tiltR;
    const seatI = seats.solidI + seats.likelyI + seats.leanI + seats.tiltI;
    const summaryHTML = `
        <span style="color:#577ccc"><b>D: ${seatD + seats.DEM}</b>  ${netStr(gains, losses, "DEM", "#577ccc")}</span>
        &nbsp;|&nbsp;
        <span style="color:#d22532"><b>R: ${seatR + seats.REP}</b>  ${netStr(gains, losses, "REP", "#d22532")}</span>
        ${seatI ? `<span style="color:#8e20c7"><b>+ ${seatI + seats.IND} I</b> ${netStr(gains, losses, "IND", "#8e20c7")}</span>` : ""}
    `;

    return { regions, seats, summaryHTML, filteredPolls };
}

const owner  = process.env.GITHUB_OWNER;
const repo   = process.env.GITHUB_REPO;
const branch = process.env.GITHUB_BRANCH;                   
const folder = process.env.GITHUB_FOLDER;   
const path   = `${folder}/results_${new Date().toISOString().split("T")[0]}.json`;;   

async function uploadToGitHub(content, path = `${folder}/results_${new Date().toISOString().split("T")[0]}.json`) {
    const token = process.env.GITHUB_TOKEN;
    if (!token) throw new Error("GITHUB_TOKEN env var is not set");

    const apiUrl = `https://api.github.com/repos/${owner}/${repo}/contents/${path}`;
    const headers = {
        "Authorization": `Bearer ${token}`,
        "Accept":        "application/vnd.github+json",
        "Content-Type":  "application/json",
        "X-GitHub-Api-Version": "2022-11-28",
    };

    let sha;
    const existing = await fetch(`${apiUrl}?ref=${branch}`, { headers });
    if (existing.ok) {
        const data = await existing.json();
        sha = data.sha;
    } else if (existing.status !== 404) {
        throw new Error(`GitHub GET failed: ${existing.status} ${await existing.text()}`);
    }

    const body = {
        message: `chore: update results ${new Date().toISOString()}`,
        content: Buffer.from(content).toString("base64"),
        branch:  branch,
        ...(sha ? { sha } : {}),    
    };

    const res = await fetch(apiUrl, { method: "PUT", headers, body: JSON.stringify(body) });
    if (!res.ok) throw new Error(`GitHub PUT failed: ${res.status} ${await res.text()}`);

    console.log(`generate.js: uploaded to github → ${path}`);
}

async function main() {
    console.log("generate.js: starting pipeline runs...");
    const date = new Date().toISOString().split("T")[0]; 
    const [senate, gov, house] = await Promise.all([
        buildSenate(),
        buildGov(),
        buildHouse(),
    ]);

    const { filteredPolls: _s, ...senateFinal } = senate;
    const { filteredPolls: _g, ...govFinal }    = gov;
    const { filteredPolls: _h, ...houseFinal }  = house;

    const output = {
        generated: new Date().toISOString(),
        senate: senateFinal,
        gov:    govFinal,
        house:  houseFinal,
    };

    function cleanPoll(poll) {
        const { _normalized, _rows, ...rest } = poll;
        return rest;
    }

    await uploadToGitHub(JSON.stringify(output));

    let existingDates = [];
    try {
        const token = process.env.GITHUB_TOKEN;
        const latestApiUrl = `https://api.github.com/repos/${owner}/${repo}/contents/${folder}/latest.json?ref=${branch}`;
        const existing = await fetch(latestApiUrl, {
            headers: {
                "Authorization": `Bearer ${token}`,
                "Accept": "application/vnd.github+json",
                "X-GitHub-Api-Version": "2022-11-28",
            },
        });
        if (existing.ok) {
            const data = await existing.json();
            const parsed = JSON.parse(Buffer.from(data.content, "base64").toString("utf8"));
            if (Array.isArray(parsed.dates)) existingDates = parsed.dates;
        }
    } catch (e) {
        console.warn("generate.js: could not read existing latest.json, starting fresh dates list", e.message);
    }

    const allDates = [...new Set([...existingDates, date])].sort();
    await uploadToGitHub(
        JSON.stringify({ file: `results_${date}.json`, dates: allDates }),
        `${folder}/latest.json`
    );
    await uploadToGitHub(JSON.stringify(senate.filteredPolls.map(cleanPoll)), `polls/senate_${date}.json`);
    await uploadToGitHub(JSON.stringify(gov.filteredPolls.map(cleanPoll)), `polls/gov_${date}.json`);
    await uploadToGitHub(JSON.stringify(house.filteredPolls.map(cleanPoll)), `polls/house_${date}.json`);
}

main().catch(err => { console.error(err); process.exit(1); });