FROM node:24-alpine

# Create app directory
WORKDIR /app

# Install dependencies first (better caching)
COPY package*.json ./
RUN npm ci --omit=dev

# Copy entire repo into container
COPY . .

# Optional: ensure Node runs in production mode
ENV NODE_ENV=production

# Run scheduler directly
CMD ["node", "scheduler.js"]