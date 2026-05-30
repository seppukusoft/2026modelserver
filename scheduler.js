import { spawn } from "child_process";
import { resolve, dirname } from "path";
import { fileURLToPath } from "url";

const __dirname = dirname(fileURLToPath(import.meta.url));
const script = resolve(__dirname, "generate.js");

function run() {
    console.log(`[${new Date().toISOString()}] Running generate.js...`);
    const child = spawn("node", [script], { stdio: "inherit" });
    child.on("exit", code => {
        if (code !== 0) {
            console.log(`[${new Date().toISOString()}] Exited with code ${code}`);
        }
        else {
            console.log(`[${new Date().toISOString()}] Completed`);
        }
    });
}

run(); 
setInterval(run, 30 * 60 * 1000);