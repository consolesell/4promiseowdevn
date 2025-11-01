// Persistent storage
const storage = {
    get(key) {
        return localStorage.getItem(key);
    },
    set(key, value) {
        localStorage.setItem(key, value);
    }
};

// Load from storage
document.getElementById('appId').value = storage.get('appId') || '';
document.getElementById('token').value = storage.get('token') || '';
document.getElementById('symbol').value = storage.get('symbol') || 'R_10';
document.getElementById('stake').value = storage.get('stake') || '1';
document.getElementById('duration').value = storage.get('duration') || '1';

// Save to storage on change
['appId', 'token', 'symbol', 'stake', 'duration'].forEach(id => {
    document.getElementById(id).addEventListener('change', (e) => {
        storage.set(id, e.target.value);
    });
});

// Global variables
let ws = null;
let reconnectInterval = null;
let isConnected = false;
let isBotRunning = false;
let tickHistory = [];
let tradeHistory = [];

// Enhanced Q-Table with epsilon-greedy exploration
const defaultQTable = {
    odd: { odd: 0.5, even: 0.5 },
    even: { odd: 0.5, even: 0.5 }
};

// Deep Q-Table: Multi-state representation
const defaultDeepQTable = {};
for (let volatility of ['low', 'medium', 'high']) {
    for (let trend of ['bullish', 'neutral', 'bearish']) {
        for (let streak of ['short', 'medium', 'long']) {
            defaultDeepQTable[`${volatility}_${trend}_${streak}`] = { odd: 0.5, even: 0.5 };
        }
    }
}

let qTable;
let deepQTable;
try {
    qTable = JSON.parse(storage.get('qTable'));
    deepQTable = JSON.parse(storage.get('deepQTable'));
} catch (e) {
    qTable = null;
    deepQTable = null;
}

if (!qTable || typeof qTable !== 'object') {
    qTable = JSON.parse(JSON.stringify(defaultQTable));
}
if (!deepQTable || typeof deepQTable !== 'object') {
    deepQTable = JSON.parse(JSON.stringify(defaultDeepQTable));
}

const MAX_HISTORY = 5000;
let currentContractId = null;
let balanceSubscriptionId = null;

// Enhanced learning parameters with adaptive decay
const baseLearningRate = 0.15;
const learningRateDecay = 0.9995;
let currentLearningRate = baseLearningRate;
const discountFactor = 0.92;
const baseConfidenceThreshold = 0.57;
const epsilon = 0.0;
const cooldownMs = 5000;
let nextTradeTime = 0;
let isPending = false;
let wins = 0;
let losses = 0;
let consecutiveLosses = 0;
const martingaleMultiplier = 2;

// Advanced pattern recognition memory
let patternMemory = [];
try {
    patternMemory = JSON.parse(storage.get('patternMemory')) || [];
} catch (e) {
    patternMemory = [];
}

// Performance tracking for model weighting
let modelPerformance = {
    stat: { correct: 0, total: 0 },
    markov: { correct: 0, total: 0 },
    trend: { correct: 0, total: 0 },
    qlearning: { correct: 0, total: 0 },
    streak: { correct: 0, total: 0 },
    pattern: { correct: 0, total: 0 },
    entropy: { correct: 0, total: 0 },
    cycle: { correct: 0, total: 0 }
};
try {
    const savedPerformance = JSON.parse(storage.get('modelPerformance'));
    if (savedPerformance) modelPerformance = savedPerformance;
} catch (e) {}

// ===== NEW: Meta-Reasoning Layer =====
let reasoningHealth = {
    confidenceVariance: [],
    recentWinRate: 0,
    modelDisagreement: 0,
    lastHealthScore: 1.0
};

// ===== NEW: Contextual Memory =====
let contextMemory = [];
try {
    contextMemory = JSON.parse(storage.get('contextMemory')) || [];
} catch (e) {
    contextMemory = [];
}

// ===== NEW: Meta-Q-Table for strategy learning =====
let metaQTable = {};
for (let vol of ['low', 'medium', 'high']) {
    for (let ent of ['low', 'medium', 'high']) {
        metaQTable[`${vol}_${ent}`] = {
            conservative: 0.5,
            balanced: 0.5,
            aggressive: 0.5
        };
    }
}
try {
    const saved = JSON.parse(storage.get('metaQTable'));
    if (saved) metaQTable = saved;
} catch (e) {}

// ===== NEW: Smoothed confidence tracking =====
let smoothedConfidence = 0.5;

// ===== NEW: Data integrity tracking =====
let dataIntegrity = {
    score: 1.0,
    recentAnomalies: 0
};

// ===== NEW: Strategy mode =====
let currentMode = 'balanced'; // 'precision', 'exploration', 'balanced'

const log = (message, type = '') => {
    const logEl = document.getElementById('log');
    const timestamp = new Date().toLocaleTimeString();
    const className = type ? `class="${type}"` : '';
    logEl.innerHTML += `<div ${className}>[${timestamp}] ${message}</div>\n`;
    logEl.scrollTop = logEl.scrollHeight;
};

const updateStatus = (text, type) => {
    const statusEl = document.getElementById('status');
    statusEl.textContent = text;
    statusEl.className = `status ${type}`;
};

const updateUI = () => {
    document.getElementById('lastTick').textContent = tickHistory.length > 0 ? tickHistory[tickHistory.length - 1].quote.toFixed(2) : '-';
    document.getElementById('lastDigit').textContent = tickHistory.length > 0 ? tickHistory[tickHistory.length - 1].digit : '-';
    
    const recent = tickHistory.slice(-10);
    const odds = recent.filter(t => t.digit % 2 === 1).length;
    document.getElementById('recentOdds').textContent = odds;
    
    const historyList = document.getElementById('historyList');
    historyList.innerHTML = tickHistory.slice(-MAX_HISTORY).map(t => `<div class="history-item">Tick: ${t.quote.toFixed(2)} (Digit: ${t.digit})</div>`).join('');
};

const updateTradeStats = () => {
    document.getElementById('wins').textContent = wins;
    document.getElementById('losses').textContent = losses;
    const totalTrades = wins + losses;
    document.getElementById('winRate').textContent = totalTrades > 0 ? `${(wins / totalTrades * 100).toFixed(1)}%` : '-';
};

// ===== NEW: Calculate Reasoning Health Score =====
const calculateReasoningHealth = () => {
    const recent20 = tradeHistory.slice(-20);
    if (recent20.length < 10) return 1.0;
    
    // Confidence variance
    const confidences = recent20.map(t => t.confidence);
    const avgConf = confidences.reduce((a, b) => a + b) / confidences.length;
    const variance = confidences.reduce((sum, c) => sum + Math.pow(c - avgConf, 2), 0) / confidences.length;
    
    // Win rate calculation
    let recentWins = 0;
    for (let i = 0; i < recent20.length - 1; i++) {
        const trade = recent20[i];
        const tradeIndex = tradeHistory.indexOf(trade);
        if (tradeIndex >= 0 && tradeIndex < tradeHistory.length - 1) {
            const nextTrade = tradeHistory[tradeIndex + 1];
            if (nextTrade.profit !== undefined && nextTrade.profit > 0) recentWins++;
        }
    }
    const recentWinRate = recentWins / Math.max(1, recent20.length - 1);
    const winRateDrift = Math.abs(recentWinRate - 0.5);
    
    // Model disagreement
    const weightVariances = recent20.map(t => {
        if (!t.weights) return 0;
        const weights = Object.values(t.weights);
        const maxWeight = Math.max(...weights);
        const minWeight = Math.min(...weights);
        return maxWeight - minWeight;
    });
    const avgDisagreement = weightVariances.reduce((a, b) => a + b, 0) / weightVariances.length;
    
    // Health score (0-1, higher is better)
    const healthScore = Math.max(0.3, 
        1.0 - (variance * 2) - (winRateDrift * 1.5) - (avgDisagreement * 0.5)
    );
    
    reasoningHealth.lastHealthScore = healthScore;
    reasoningHealth.recentWinRate = recentWinRate;
    reasoningHealth.modelDisagreement = avgDisagreement;
    
    return healthScore;
};

// ===== NEW: Dynamic Confidence Threshold =====
const getAdaptiveConfidenceThreshold = () => {
    const health = calculateReasoningHealth();
    let threshold = baseConfidenceThreshold;
    
    if (health < 0.6) {
        threshold += 0.08;
        log(`⚠️ Low reasoning health (${(health * 100).toFixed(0)}%) - raising threshold to ${(threshold * 100).toFixed(1)}%`);
    } else if (health > 0.85) {
        threshold -= 0.03;
    }
    
    // Adjust based on recent entropy
    if (tickHistory.length >= 50) {
        const recentEntropy = calculateEntropy(tickHistory, 50);
        if (recentEntropy > 0.9) {
            threshold += 0.05;
        }
    }
    
    return Math.min(0.75, Math.max(0.52, threshold));
};

// ===== NEW: Store Context for Memory =====
const storeContext = (trade, result) => {
    contextMemory.push({
        volatility: trade.volatility,
        entropy: trade.entropy,
        streak: trade.streak,
        confidence: trade.confidence,
        prediction: trade.prediction,
        result: result,
        timestamp: trade.timestamp
    });
    
    if (contextMemory.length > 500) {
        contextMemory = contextMemory.slice(-300);
    }
    storage.set('contextMemory', JSON.stringify(contextMemory));
};

// ===== NEW: Find Similar Historical Context =====
const findSimilarContext = (currentVolatility, currentEntropy, currentStreak) => {
    if (contextMemory.length < 20) return null;
    
    let bestMatch = null;
    let bestSimilarity = 0;
    
    contextMemory.slice(-100).forEach(ctx => {
        const volDiff = Math.abs(ctx.volatility - currentVolatility);
        const entDiff = Math.abs(ctx.entropy - currentEntropy);
        const streakDiff = Math.abs(ctx.streak - currentStreak);
        
        const similarity = 1 - (volDiff + entDiff + streakDiff * 0.1) / 3;
        
        if (similarity > bestSimilarity && similarity > 0.7) {
            bestSimilarity = similarity;
            bestMatch = ctx;
        }
    });
    
    return bestMatch ? {
        suggestedAction: bestMatch.prediction,
        historicalResult: bestMatch.result,
        similarity: bestSimilarity,
        confidence: bestMatch.confidence
    } : null;
};

// ===== NEW: Bayesian Confidence Fusion =====
const bayesianFusion = (modelProbs, modelWeights) => {
    let posteriorOdd = 0.5;
    let posteriorEven = 0.5;
    
    Object.keys(modelProbs).forEach(model => {
        const weight = modelWeights[model] || 0.125;
        posteriorOdd += weight * modelProbs[model].odd;
        posteriorEven += weight * modelProbs[model].even;
    });
    
    // Normalize
    const total = posteriorOdd + posteriorEven;
    return {
        odd: posteriorOdd / total,
        even: posteriorEven / total
    };
};

// ===== NEW: Adaptive Learning Rate & Threshold Tuning =====
const autoTuneLearningParameters = () => {
    const totalTrades = wins + losses;
    if (totalTrades < 10) return;
    
    const winRate = wins / totalTrades;
    const recentEntropy = tickHistory.length >= 50 ? calculateEntropy(tickHistory, 50) : 0.8;
    
    // Adjust learning rate
    if (winRate < 0.45) {
        currentLearningRate = Math.min(baseLearningRate * 1.2, currentLearningRate * 1.05);
        log(`📈 Increasing learning rate to ${currentLearningRate.toFixed(4)} due to low win rate`);
    } else if (winRate > 0.55) {
        currentLearningRate = Math.max(0.01, currentLearningRate * learningRateDecay);
    }
    
    // Mode switching based on entropy
    if (recentEntropy > 0.9 && currentMode !== 'exploration') {
        currentMode = 'exploration';
        log(`🔄 Switching to EXPLORATION mode (high entropy: ${recentEntropy.toFixed(2)})`);
    } else if (recentEntropy < 0.7 && currentMode !== 'precision') {
        currentMode = 'precision';
        log(`🎯 Switching to PRECISION mode (low entropy: ${recentEntropy.toFixed(2)})`);
    } else if (recentEntropy >= 0.7 && recentEntropy <= 0.9 && currentMode !== 'balanced') {
        currentMode = 'balanced';
        log(`⚖️ Switching to BALANCED mode (entropy: ${recentEntropy.toFixed(2)})`);
    }
};

// ===== NEW: Cross-Model Validation =====
const checkModelConsensus = (modelPredictions) => {
    const predictions = Object.values(modelPredictions);
    const oddCount = predictions.filter(p => p === 'odd').length;
    const evenCount = predictions.filter(p => p === 'even').length;
    
    const agreement = Math.max(oddCount, evenCount) / predictions.length;
    const dominantPrediction = oddCount > evenCount ? 'odd' : 'even';
    
    return {
        agreement: agreement,
        prediction: dominantPrediction,
        hasConsensus: agreement >= 0.6
    };
};

// ===== NEW: Tick Anomaly Detection =====
const validateTickData = (newTick, previousTick) => {
    if (!previousTick) return true;
    
    const priceChange = Math.abs(newTick.quote - previousTick.quote);
    const recentVolatility = tickHistory.length >= 20 ? calculateVolatility(tickHistory, 20) : 1;
    
    // Check for extreme price movement
    const threshold = recentVolatility * 5;
    if (priceChange > threshold) {
        dataIntegrity.recentAnomalies++;
        dataIntegrity.score = Math.max(0.5, dataIntegrity.score * 0.95);
        log(`⚠️ Tick anomaly detected: price change ${priceChange.toFixed(4)} exceeds threshold ${threshold.toFixed(4)}`);
        return false;
    }
    
    // Gradual recovery of integrity score
    if (dataIntegrity.recentAnomalies > 0) {
        dataIntegrity.recentAnomalies = Math.max(0, dataIntegrity.recentAnomalies - 0.1);
        dataIntegrity.score = Math.min(1.0, dataIntegrity.score + 0.01);
    }
    
    return true;
};

// ===== NEW: Predictive Cooling System =====
const shouldEnterCooldown = () => {
    if (consecutiveLosses < 3) return false;
    
    const recentEntropy = tickHistory.length >= 50 ? calculateEntropy(tickHistory, 50) : 0.8;
    
    if (consecutiveLosses >= 3 && recentEntropy > 0.9) {
        const cooldownTicks = 5 + consecutiveLosses;
        log(`🧊 Entering predictive cooldown for ${cooldownTicks} ticks (losses: ${consecutiveLosses}, entropy: ${recentEntropy.toFixed(2)})`);
        nextTradeTime = Date.now() + (cooldownTicks * 2000);
        return true;
    }
    
    return false;
};

// ===== NEW: Update Meta-Q-Table =====
const updateMetaQTable = (volatilityState, entropyState, strategy, reward) => {
    const state = `${volatilityState}_${entropyState}`;
    if (!metaQTable[state]) return;
    
    const alpha = 0.1;
    const gamma = 0.9;
    
    const currentQ = metaQTable[state][strategy];
    const maxNextQ = Math.max(...Object.values(metaQTable[state]));
    
    metaQTable[state][strategy] = currentQ + alpha * (reward + gamma * maxNextQ - currentQ);
    
    storage.set('metaQTable', JSON.stringify(metaQTable));
};

// ===== NEW: Select Strategy from Meta-Q =====
const selectStrategy = (volatility, entropy) => {
    const volState = volatility < 0.3 ? 'low' : volatility < 0.7 ? 'medium' : 'high';
    const entState = entropy < 0.7 ? 'low' : entropy < 0.9 ? 'medium' : 'high';
    const state = `${volState}_${entState}`;
    
    if (!metaQTable[state]) return 'balanced';
    
    const strategies = metaQTable[state];
    const bestStrategy = Object.keys(strategies).reduce((a, b) => 
        strategies[a] > strategies[b] ? a : b
    );
    
    return bestStrategy;
};

// Enhanced: Calculate Exponential Moving Average
const calculateEMA = (data, window, alpha = null) => {
    if (data.length < window) return 0;
    if (!alpha) alpha = 2 / (window + 1);
    let ema = data[data.length - window].quote;
    for (let i = data.length - window + 1; i < data.length; i++) {
        ema = alpha * data[i].quote + (1 - alpha) * ema;
    }
    return ema;
};

// Enhanced: Calculate moving average
const calculateMovingAverage = (data, window) => {
    if (data.length < window) return 0;
    return data.slice(-window).reduce((sum, tick) => sum + tick.quote, 0) / window;
};

// Enhanced: Calculate volatility with exponential weighting
const calculateVolatility = (data, window) => {
    if (data.length < window) return 0;
    const ema = calculateEMA(data, window);
    const variance = data.slice(-window).reduce((sum, tick, idx) => {
        const weight = Math.exp(-0.1 * (window - idx - 1));
        return sum + weight * Math.pow(tick.quote - ema, 2);
    }, 0) / window;
    return Math.sqrt(variance);
};

// Enhanced: Advanced Markov chain with higher-order transitions
const calculateMarkovProbabilities = (history) => {
    if (history.length < 3) return { oddToOdd: 0.5, oddToEven: 0.5, evenToOdd: 0.5, evenToEven: 0.5 };
    
    let transitions = { oddToOdd: 0, oddToEven: 0, evenToOdd: 0, evenToEven: 0 };
    let counts = { odd: 0, even: 0 };
    
    let secondOrder = {};
    
    for (let i = 1; i < history.length; i++) {
        const prev = history[i - 1].digit % 2 === 1 ? 'odd' : 'even';
        const curr = history[i].digit % 2 === 1 ? 'odd' : 'even';
        counts[prev]++;
        transitions[`${prev}To${curr.charAt(0).toUpperCase() + curr.slice(1)}`]++;
        
        if (i >= 2) {
            const prevPrev = history[i - 2].digit % 2 === 1 ? 'odd' : 'even';
            const key = `${prevPrev}_${prev}`;
            if (!secondOrder[key]) secondOrder[key] = { odd: 0, even: 0, total: 0 };
            secondOrder[key][curr]++;
            secondOrder[key].total++;
        }
    }
    
    return {
        oddToOdd: transitions.oddToOdd / (counts.odd || 1),
        oddToEven: transitions.oddToEven / (counts.odd || 1),
        evenToOdd: transitions.evenToOdd / (counts.even || 1),
        evenToEven: transitions.evenToEven / (counts.even || 1),
        secondOrder: secondOrder
    };
};

// Calculate entropy (randomness measure)
const calculateEntropy = (history, window = 20) => {
    if (history.length < window) return 0;
    const recent = history.slice(-window);
    const digitCounts = Array(10).fill(0);
    recent.forEach(t => digitCounts[t.digit]++);
    
    let entropy = 0;
    digitCounts.forEach(count => {
        if (count > 0) {
            const p = count / window;
            entropy -= p * Math.log2(p);
        }
    });
    return entropy / Math.log2(10);
};

// Detect cyclic patterns
const detectCyclicPattern = (history, maxPeriod = 10) => {
    if (history.length < maxPeriod * 2) return { hasCycle: false, period: 0, strength: 0 };
    
    const sequence = history.slice(-maxPeriod * 3).map(t => t.digit % 2);
    let bestPeriod = 0;
    let bestScore = 0;
    
    for (let period = 2; period <= maxPeriod; period++) {
        let matches = 0;
        let total = 0;
        for (let i = period; i < sequence.length; i++) {
            if (sequence[i] === sequence[i - period]) matches++;
            total++;
        }
        const score = matches / total;
        if (score > bestScore) {
            bestScore = score;
            bestPeriod = period;
        }
    }
    
    return {
        hasCycle: bestScore > 0.65,
        period: bestPeriod,
        strength: bestScore
    };
};

// Enhanced: Calculate current streak with momentum
const calculateStreak = (history) => {
    if (history.length < 2) return { length: 0, type: null, momentum: 0 };
    let length = 1;
    const lastType = history[history.length - 1].digit % 2 === 1 ? 'odd' : 'even';
    for (let i = history.length - 2; i >= 0; i--) {
        const currentType = history[i].digit % 2 === 1 ? 'odd' : 'even';
        if (currentType === lastType) {
            length++;
        } else {
            break;
        }
    }
    
    let momentum = 0;
    if (history.length >= 10) {
        const recent10 = history.slice(-10);
        const typeCount = recent10.filter(t => (t.digit % 2 === 1 ? 'odd' : 'even') === lastType).length;
        momentum = (typeCount / 10) - 0.5;
    }
    
    return { length, type: lastType, momentum };
};

// Pattern matching with historical success
const findSimilarPatterns = (currentPattern, history) => {
    if (history.length < 10 || patternMemory.length === 0) return null;
    
    const patternLength = 5;
    const current = currentPattern.slice(-patternLength).map(t => t.digit % 2);
    
    let bestMatch = null;
    let bestSimilarity = 0;
    
    patternMemory.forEach(patternItem => {
        if (patternItem.sequence.length !== patternLength) return;
        
        let similarity = 0;
        for (let i = 0; i < patternLength; i++) {
            if (patternItem.sequence[i] === current[i]) similarity++;
        }
        similarity /= patternLength;
        
        if (similarity > bestSimilarity && similarity >= 0.8) {
            bestSimilarity = similarity;
            bestMatch = patternItem;
        }
    });
    
    return bestMatch ? {
        nextPrediction: bestMatch.nextOutcome,
        confidence: bestSimilarity * bestMatch.successRate,
        successRate: bestMatch.successRate
    } : null;
};

// Store successful patterns
const storePattern = (sequence, outcome, wasCorrect) => {
    const patternKey = sequence.join('');
    let existing = patternMemory.find(p => p.sequence.join('') === patternKey);
    
    if (existing) {
        existing.occurrences++;
        existing.successes += wasCorrect ? 1 : 0;
        existing.successRate = existing.successes / existing.occurrences;
        if (wasCorrect) existing.nextOutcome = outcome;
    } else {
        patternMemory.push({
            sequence: sequence,
            nextOutcome: outcome,
            occurrences: 1,
            successes: wasCorrect ? 1 : 0,
            successRate: wasCorrect ? 1 : 0
        });
    }
    
    if (patternMemory.length > 100) {
        patternMemory.sort((a, b) => (b.successRate * b.occurrences) - (a.successRate * a.occurrences));
        patternMemory = patternMemory.slice(0, 100);
    }
    
    storage.set('patternMemory', JSON.stringify(patternMemory));
};

// Enhanced: Deep state representation
const getDeepState = (volatility, trend, streak) => {
    const volState = volatility < 0.3 ? 'low' : volatility < 0.7 ? 'medium' : 'high';
    const trendState = trend > 0.05 ? 'bullish' : trend < -0.05 ? 'bearish' : 'neutral';
    const streakState = streak < 3 ? 'short' : streak < 6 ? 'medium' : 'long';
    return `${volState}_${trendState}_${streakState}`;
};

// Enhanced: Update Q-table
const updateQTable = (state, action, reward, deepState = null) => {
    qTable[state][action] = qTable[state][action] + currentLearningRate * (reward - qTable[state][action]);
    
    if (deepState && deepQTable[deepState]) {
        deepQTable[deepState][action] = deepQTable[deepState][action] + 
            currentLearningRate * (reward + discountFactor * Math.max(deepQTable[deepState].odd, deepQTable[deepState].even) - deepQTable[deepState][action]);
    }
    
    currentLearningRate = Math.max(0.01, currentLearningRate * learningRateDecay);
    
    storage.set('qTable', JSON.stringify(qTable));
    storage.set('deepQTable', JSON.stringify(deepQTable));
    log(`Updated Q-tables (LR=${currentLearningRate.toFixed(4)}): Simple[${state}]=${qTable[state].odd.toFixed(3)}/${qTable[state].even.toFixed(3)}`);
};

// Update model performance tracking
const updateModelPerformance = (predictions, actualOutcome) => {
    Object.keys(predictions).forEach(model => {
        if (modelPerformance[model]) {
            modelPerformance[model].total++;
            if (predictions[model] === actualOutcome) {
                modelPerformance[model].correct++;
            }
        }
    });
    storage.set('modelPerformance', JSON.stringify(modelPerformance));
};

// Calculate adaptive weights based on performance
const getAdaptiveWeights = () => {
    const weights = {};
    let totalAccuracy = 0;
    
    Object.keys(modelPerformance).forEach(model => {
        const perf = modelPerformance[model];
        const accuracy = perf.total > 0 ? perf.correct / perf.total : 0.5;
        weights[model] = Math.pow(accuracy, 2);
        totalAccuracy += weights[model];
    });
    
    Object.keys(weights).forEach(model => {
        weights[model] = totalAccuracy > 0 ? weights[model] / totalAccuracy : 1 / Object.keys(weights).length;
    });
    
    Object.keys(weights).forEach(model => {
        weights[model] = Math.max(0.05, weights[model]);
    });
    
    totalAccuracy = Object.values(weights).reduce((sum, w) => sum + w, 0);
    Object.keys(weights).forEach(model => {
        weights[model] = weights[model] / totalAccuracy;
    });
    
    return weights;
};

const connect = () => {
    const appId = document.getElementById('appId').value;
    const token = document.getElementById('token').value;
    if (!appId || !token) {
        log('Error: App ID and Token are required.', 'error');
        return;
    }

    if (ws) ws.close();

    ws = new WebSocket(`wss://ws.derivws.com/websockets/v3?app_id=${appId}`);
    
    ws.onopen = () => {
        log('Connected to Deriv API.');
        ws.send(JSON.stringify({ authorize: token }));
    };

    ws.onmessage = (event) => {
        const data = JSON.parse(event.data);
        const msgType = data.msg_type;
        const error = data.error;

        if (error) {
            log(`Error: ${error.message}`, 'error');
            if (msgType === 'proposal') {
                isPending = false;
            }
            return;
        }

        if (msgType === 'authorize') {
            isConnected = true;
            updateStatus('Connected & Authorized', 'connected');
            log(`Authorized. Balance: ${data.authorize.balance}`);
            document.getElementById('balance').textContent = `$${data.authorize.balance}`;
            document.getElementById('connectBtn').disabled = true;
            document.getElementById('startBtn').disabled = false;
            document.getElementById('stopBtn').disabled = false;
            
            if (balanceSubscriptionId) {
                ws.send(JSON.stringify({ forget: balanceSubscriptionId }));
            }
            ws.send(JSON.stringify({ balance: 1, subscribe: 1 }));
            
            const symbol = document.getElementById('symbol').value;
            isBotRunning = false;
            
            ws.send(JSON.stringify({
                ticks_history: symbol,
                end: 'latest',
                count: 5000,
                style: 'ticks'
            }));
            log(`Fetching 5000 historical ticks for ${symbol}.`);
        } else if (msgType === 'history') {
            const history = data.history;
            if (history && history.times && history.prices) {
                const historicalTicks = [];
                for (let i = 0; i < history.times.length; i++) {
                    const epoch = history.times[i];
                    const quote = parseFloat(history.prices[i]);
                    if (isNaN(quote)) continue;
                    const digit = Math.floor(quote * 100) % 10;
                    historicalTicks.push({ epoch, quote, digit });
                }
                tickHistory = historicalTicks.concat(tickHistory);
                if (tickHistory.length > MAX_HISTORY) {
                    tickHistory = tickHistory.slice(-MAX_HISTORY);
                }
                log(`Loaded ${historicalTicks.length} historical ticks. Total history: ${tickHistory.length}`);
                updateUI();
                
                const symbol = document.getElementById('symbol').value;
                ws.send(JSON.stringify({ ticks: symbol, subscribe: 1 }));
                log(`Subscribed to real-time ticks for ${symbol}.`);
            }
        } else if (msgType === 'balance') {
            document.getElementById('balance').textContent = `$${data.balance.balance}`;
        } else if (msgType === 'tick') {
            const quote = parseFloat(data.tick.quote);
            if (isNaN(quote)) {
                log('Invalid tick quote received.', 'error');
                return;
            }
            const digit = Math.floor(quote * 100) % 10;
            const newTick = { ...data.tick, quote, digit };
            
            if (tickHistory.length === 0 || newTick.epoch > tickHistory[tickHistory.length - 1].epoch) {
                // NEW: Validate tick data
                const previousTick = tickHistory.length > 0 ? tickHistory[tickHistory.length - 1] : null;
                const isValid = validateTickData(newTick, previousTick);
                
                tickHistory.push(newTick);
                if (tickHistory.length > MAX_HISTORY) {
                    tickHistory.shift();
                }
                updateUI();
                
                // NEW: Auto-tune learning parameters periodically
                if (tickHistory.length % 50 === 0) {
                    autoTuneLearningParameters();
                }
                
                if (isBotRunning && !currentContractId && Date.now() >= nextTradeTime && !isPending && isValid) {
                    // NEW: Check cooldown conditions
                    if (!shouldEnterCooldown()) {
                        setTimeout(() => analyzeAndTrade(data.tick), 100);
                    }
                }
            }
        } else if (msgType === 'proposal') {
            const proposal = data.proposal;
            if (proposal && proposal.id) {
                ws.send(JSON.stringify({
                    buy: proposal.id,
                    price: proposal.ask_price
                }));
                log(`Bought contract for ${proposal.contract_type} at ${proposal.ask_price}`);
            } else {
                isPending = false;
            }
        } else if (msgType === 'buy') {
            currentContractId = data.buy.contract_id;
            isPending = false;
            log(`Contract purchased: ID ${currentContractId}`);
            
            ws.send(JSON.stringify({
                proposal_open_contract: 1,
                contract_id: currentContractId,
                subscribe: 1
            }));
        } else if (msgType === 'proposal_open_contract') {
            const contract = data.proposal_open_contract;
            if (contract.contract_id === currentContractId && (contract.is_sold || contract.status === 'sold')) {
                const profit = contract.profit;
                log(`Contract ${currentContractId} closed. Profit: ${profit} (Payout: ${contract.payout})`, profit > 0 ? 'success' : 'error');
                const reward = profit > 0 ? 1 : -1;
                const actualOutcome = profit > 0 ? 'correct' : 'incorrect';
                
                if (profit > 0) {
                    wins++;
                    consecutiveLosses = 0;
                } else {
                    losses++;
                    consecutiveLosses++;
                }
                updateTradeStats();
                
                const lastTrade = tradeHistory[tradeHistory.length - 1];
                if (lastTrade) {
                    // Store profit for future analysis
                    lastTrade.profit = profit;
                    
                    updateQTable(lastTrade.state, lastTrade.prediction, reward, lastTrade.deepState);
                    
                    if (lastTrade.modelPredictions) {
                        const actual = lastTrade.prediction;
                        updateModelPerformance(lastTrade.modelPredictions, actual);
                    }
                    
                    // NEW: Store context memory
                    storeContext(lastTrade, profit > 0 ? 'win' : 'loss');
                    
                    // NEW: Update meta-Q-table
                    const volState = lastTrade.volatility < 0.3 ? 'low' : lastTrade.volatility < 0.7 ? 'medium' : 'high';
                    const entState = lastTrade.entropy < 0.7 ? 'low' : lastTrade.entropy < 0.9 ? 'medium' : 'high';
                    updateMetaQTable(volState, entState, currentMode, reward);
                    
                    if (tickHistory.length >= 6) {
                        const patternSeq = tickHistory.slice(-6, -1).map(t => t.digit % 2);
                        const outcome = lastTrade.prediction;
                        storePattern(patternSeq, outcome, profit > 0);
                    }
                }
                
                currentContractId = null;
                nextTradeTime = Date.now() + cooldownMs;
                ws.send(JSON.stringify({ forget: data.subscription.id }));
            }
        }
    };

    ws.onclose = () => {
        isConnected = false;
        updateStatus('Disconnected', 'disconnected');
        log('Connection closed. Attempting reconnect...');
        document.getElementById('connectBtn').disabled = false;
        document.getElementById('startBtn').disabled = true;
        document.getElementById('stopBtn').disabled = true;
        
        if (reconnectInterval) clearInterval(reconnectInterval);
        reconnectInterval = setTimeout(connect, 5000);
    };

    ws.onerror = (error) => {
        log(`WebSocket error: ${error}`, 'error');
    };
};

const analyzeAndTrade = (lastTick) => {
    if (tickHistory.length < 30) {
        log('Not enough history for advanced analysis. Waiting...');
        return;
    }
    isPending = true;

    const recent = tickHistory.slice(-500);
    const lastDigitNum = recent[recent.length - 1].digit;
    const state = lastDigitNum % 2 === 1 ? 'odd' : 'even';

    // === Model 1: Enhanced Statistical Probability ===
    const oddCount = recent.filter(t => t.digit % 2 === 1).length;
    const evenCount = recent.length - oddCount;
    let statProbOdd = oddCount / recent.length;
    let statProbEven = evenCount / recent.length;
    
    const deviation = Math.abs(statProbOdd - 0.5);
    if (deviation > 0.15) {
        const reversionFactor = 0.1;
        statProbOdd += (statProbOdd < 0.5 ? reversionFactor : -reversionFactor);
        statProbEven = 1 - statProbOdd;
    }

    // === Model 2: Advanced Markov Chain ===
    const markovProbs = calculateMarkovProbabilities(recent);
    let markovProbOdd = state === 'odd' ? markovProbs.oddToOdd : markovProbs.evenToOdd;
    let markovProbEven = state === 'odd' ? markovProbs.oddToEven : markovProbs.evenToEven;
    
    if (recent.length >= 3 && markovProbs.secondOrder) {
        const prevPrev = recent[recent.length - 2].digit % 2 === 1 ? 'odd' : 'even';
        const key = `${prevPrev}_${state}`;
        if (markovProbs.secondOrder[key] && markovProbs.secondOrder[key].total > 5) {
            const so = markovProbs.secondOrder[key];
            markovProbOdd = (markovProbOdd + so.odd / so.total) / 2;
            markovProbEven = (markovProbEven + so.even / so.total) / 2;
        }
    }

    // === Model 3: Enhanced Trend Analysis ===
    const volatility = calculateVolatility(recent, 50);
    const emaShort = calculateEMA(recent, 10);
    const emaLong = calculateEMA(recent, 50);
    const trendStrength = (emaShort - emaLong) / emaLong;
    const trendScore = Math.tanh(trendStrength * 10) * 0.1;
    const volatilityAdjustment = volatility > 0.6 ? -0.08 : volatility < 0.3 ? 0.05 : 0;

    // === Model 4: Deep Q-Learning ===
    const qProbOdd = qTable[state].odd;
    const qProbEven = qTable[state].even;
    
    const deepState = getDeepState(volatility, trendStrength, calculateStreak(recent).length);
    let deepQProbOdd = 0.5;
    let deepQProbEven = 0.5;
    if (deepQTable[deepState]) {
        deepQProbOdd = deepQTable[deepState].odd;
        deepQProbEven = deepQTable[deepState].even;
    }
    
    const blendedQOdd = (qProbOdd * 0.4 + deepQProbOdd * 0.6);
    const blendedQEven = (qProbEven * 0.4 + deepQProbEven * 0.6);

    // === Model 5: Advanced Streak Analysis ===
    const streak = calculateStreak(recent);
    let streakAdjustmentOdd = 0;
    let streakAdjustmentEven = 0;
    
    if (streak.length > 3) {
        const streakPenalty = Math.log(streak.length - 2) * 0.12;
        const momentumBonus = streak.momentum * 0.08;
        
        if (streak.type === 'odd') {
            streakAdjustmentOdd = -streakPenalty + momentumBonus;
            streakAdjustmentEven = streakPenalty - momentumBonus;
        } else {
            streakAdjustmentOdd = streakPenalty - momentumBonus;
            streakAdjustmentEven = -streakPenalty + momentumBonus;
        }
    }

    // === Model 6: Pattern Recognition ===
    let patternProbOdd = 0.5;
    let patternProbEven = 0.5;
    const similarPattern = findSimilarPatterns(recent, tickHistory);
    if (similarPattern && similarPattern.successRate > 0.6) {
        if (similarPattern.nextPrediction === 'odd') {
            patternProbOdd = 0.5 + similarPattern.confidence * 0.3;
            patternProbEven = 1 - patternProbOdd;
        } else {
            patternProbEven = 0.5 + similarPattern.confidence * 0.3;
            patternProbOdd = 1 - patternProbEven;
        }
        log(`Pattern match found (similarity: ${(similarPattern.confidence * 100).toFixed(1)}%, success: ${(similarPattern.successRate * 100).toFixed(1)}%)`);
    }

    // === Model 7: Entropy Analysis ===
    const entropy = calculateEntropy(recent, 50);
    let entropyAdjustmentOdd = 0;
    let entropyAdjustmentEven = 0;
    
    if (entropy > 0.9) {
        entropyAdjustmentOdd = state === 'odd' ? -0.05 : 0.05;
        entropyAdjustmentEven = state === 'even' ? -0.05 : 0.05;
    } else if (entropy < 0.7) {
        entropyAdjustmentOdd = state === 'odd' ? 0.08 : -0.08;
        entropyAdjustmentEven = state === 'even' ? 0.08 : -0.08;
    }

    // === Model 8: Cyclic Pattern Detection ===
    const cycleInfo = detectCyclicPattern(recent, 20);
    let cycleProbOdd = 0.5;
    let cycleProbEven = 0.5;
    if (cycleInfo.hasCycle && cycleInfo.strength > 0.7) {
        const cyclePrediction = recent[recent.length - cycleInfo.period].digit % 2 === 1 ? 'odd' : 'even';
        if (cyclePrediction === 'odd') {
            cycleProbOdd = 0.5 + cycleInfo.strength * 0.2;
            cycleProbEven = 1 - cycleProbOdd;
        } else {
            cycleProbEven = 0.5 + cycleInfo.strength * 0.2;
            cycleProbOdd = 1 - cycleProbEven;
        }
        log(`Cyclic pattern detected (period: ${cycleInfo.period}, strength: ${(cycleInfo.strength * 100).toFixed(1)}%)`);
    }

    // === NEW: Contextual Memory Enhancement ===
    let contextBias = 0;
    const similarContext = findSimilarContext(volatility, entropy, streak.length);
    if (similarContext && similarContext.similarity > 0.75) {
        const contextWeight = 0.1 * similarContext.similarity;
        if (similarContext.historicalResult === 'win') {
            if (similarContext.suggestedAction === 'odd') {
                contextBias = contextWeight;
            } else {
                contextBias = -contextWeight;
            }
            log(`📚 Similar context found (similarity: ${(similarContext.similarity * 100).toFixed(1)}%, prev: ${similarContext.historicalResult})`);
        }
    }

    // === Ensemble: Adaptive Weighted Combination ===
    const adaptiveWeights = getAdaptiveWeights();
    
    // Store individual model predictions for performance tracking
    const modelPredictions = {
        stat: statProbOdd > statProbEven ? 'odd' : 'even',
        markov: markovProbOdd > markovProbEven ? 'odd' : 'even',
        trend: (0.5 + trendScore + volatilityAdjustment) > 0.5 ? 'odd' : 'even',
        qlearning: blendedQOdd > blendedQEven ? 'odd' : 'even',
        streak: (0.5 + streakAdjustmentOdd) > (0.5 + streakAdjustmentEven) ? 'odd' : 'even',
        pattern: patternProbOdd > patternProbEven ? 'odd' : 'even',
        entropy: (0.5 + entropyAdjustmentOdd) > (0.5 + entropyAdjustmentEven) ? 'odd' : 'even',
        cycle: cycleProbOdd > cycleProbEven ? 'odd' : 'even'
    };

    // NEW: Check model consensus
    const consensus = checkModelConsensus(modelPredictions);
    if (!consensus.hasConsensus) {
        log(`⚠️ Low model consensus (${(consensus.agreement * 100).toFixed(0)}%) - models disagree significantly`);
    }

    // === NEW: Bayesian Fusion (Alternative to simple weighting) ===
    const modelProbs = {
        stat: { odd: statProbOdd, even: statProbEven },
        markov: { odd: markovProbOdd, even: markovProbEven },
        trend: { odd: 0.5 + trendScore + volatilityAdjustment, even: 0.5 - trendScore + volatilityAdjustment },
        qlearning: { odd: blendedQOdd, even: blendedQEven },
        streak: { odd: 0.5 + streakAdjustmentOdd, even: 0.5 + streakAdjustmentEven },
        pattern: { odd: patternProbOdd, even: patternProbEven },
        entropy: { odd: 0.5 + entropyAdjustmentOdd, even: 0.5 + entropyAdjustmentEven },
        cycle: { odd: cycleProbOdd, even: cycleProbEven }
    };

    const bayesianResult = bayesianFusion(modelProbs, adaptiveWeights);
    let finalProbOdd = bayesianResult.odd;
    let finalProbEven = bayesianResult.even;

    // Apply context bias
    finalProbOdd += contextBias;
    finalProbEven -= contextBias;

    // Add cycle influence if detected
    if (cycleInfo.hasCycle) {
        finalProbOdd = finalProbOdd * 0.85 + cycleProbOdd * 0.15;
        finalProbEven = finalProbEven * 0.85 + cycleProbEven * 0.15;
    }

    // NEW: Apply data integrity weighting
    if (dataIntegrity.score < 0.9) {
        log(`⚠️ Data integrity: ${(dataIntegrity.score * 100).toFixed(0)}%`);
        const integrityFactor = dataIntegrity.score;
        finalProbOdd = finalProbOdd * integrityFactor + 0.5 * (1 - integrityFactor);
        finalProbEven = finalProbEven * integrityFactor + 0.5 * (1 - integrityFactor);
    }

    if (isNaN(finalProbOdd) || isNaN(finalProbEven)) {
        log('Invalid probability calculation. Skipping trade.', 'error');
        isPending = false;
        return;
    }

    // Normalize probabilities
    const total = finalProbOdd + finalProbEven;
    finalProbOdd = finalProbOdd / total;
    finalProbEven = finalProbEven / total;

    // === Enhanced Decision Logic with Epsilon-Greedy Exploration ===
    let prediction;
    let rawConfidence = Math.max(finalProbOdd, finalProbEven);
    
    // NEW: Mode-based epsilon adjustment
    let modeEpsilon = epsilon;
    if (currentMode === 'exploration') {
        modeEpsilon = 0.1; // More exploration
    } else if (currentMode === 'precision') {
        modeEpsilon = 0.0; // No exploration
    }
    
    // Epsilon-greedy: Sometimes explore random actions
    if (Math.random() < modeEpsilon) {
        prediction = Math.random() < 0.5 ? 'odd' : 'even';
        rawConfidence = 0.5;
        log('🔄 Exploration mode: Random prediction for learning');
    } else {
        prediction = finalProbOdd > finalProbEven ? 'odd' : 'even';
    }

    // NEW: Apply confidence smoothing
    smoothedConfidence = 0.7 * smoothedConfidence + 0.3 * rawConfidence;
    const confidence = smoothedConfidence;

    if (isNaN(confidence)) {
        log('Invalid confidence. Skipping trade.', 'error');
        isPending = false;
        return;
    }

    log(`Advanced Analysis: Odds=${(finalProbOdd * 100).toFixed(1)}%, Evens=${(finalProbEven * 100).toFixed(1)}%, Conf=${(confidence * 100).toFixed(1)}%`);
    log(`Metrics: Entropy=${entropy.toFixed(2)}, Vol=${volatility.toFixed(2)}, Streak=${streak.length}(${streak.type}), Momentum=${streak.momentum.toFixed(2)}`);
    log(`Model Weights: Stat=${(adaptiveWeights.stat * 100).toFixed(0)}%, Markov=${(adaptiveWeights.markov * 100).toFixed(0)}%, Q=${(adaptiveWeights.qlearning * 100).toFixed(0)}%`);
    log(`🎯 Mode: ${currentMode.toUpperCase()}, Health: ${(reasoningHealth.lastHealthScore * 100).toFixed(0)}%, Consensus: ${(consensus.agreement * 100).toFixed(0)}%`);

    // === NEW: Adaptive Confidence Threshold ===
    const adaptiveThreshold = getAdaptiveConfidenceThreshold();
    
    if (confidence < adaptiveThreshold) {
        log(`Low confidence (${(confidence * 100).toFixed(1)}% < ${(adaptiveThreshold * 100).toFixed(1)}%). Skipping trade.`);
        isPending = false;
        return;
    }

    // NEW: Require consensus in precision mode
    if (currentMode === 'precision' && !consensus.hasConsensus) {
        log(`🎯 Precision mode: Insufficient consensus (${(consensus.agreement * 100).toFixed(0)}%). Skipping trade.`);
        isPending = false;
        return;
    }

    // === NEW: Strategy-based Stake Management ===
    let baseStake = parseInt(document.getElementById('stake').value);
    
    // Select strategy from meta-Q-table
    const recommendedStrategy = selectStrategy(volatility, entropy);
    let strategyMultiplier = 1.0;
    
    if (recommendedStrategy === 'conservative') {
        strategyMultiplier = 0.75;
        log(`💼 Meta-strategy: CONSERVATIVE (reducing stake by 25%)`);
    } else if (recommendedStrategy === 'aggressive' && confidence > 0.65) {
        strategyMultiplier = 1.25;
        log(`🚀 Meta-strategy: AGGRESSIVE (increasing stake by 25%)`);
    } else {
        log(`⚖️ Meta-strategy: BALANCED`);
    }
    
    // Apply martingale with strategy modifier
    let stake = baseStake * Math.pow(martingaleMultiplier, consecutiveLosses) * strategyMultiplier;
    stake = Math.round(stake);
    
    log(`Stake Calculation: Base=$${baseStake}, Losses=${consecutiveLosses}, Strategy=${strategyMultiplier.toFixed(2)}x, Final=$${stake}`);

    // === Execute Trade ===
    const contractType = prediction === 'odd' ? 'DIGITODD' : 'DIGITEVEN';
    const duration = parseInt(document.getElementById('duration').value);
    const symbol = document.getElementById('symbol').value;

    ws.send(JSON.stringify({
        proposal: 1,
        amount: stake,
        basis: 'stake',
        contract_type: contractType,
        currency: 'USD',
        duration: duration,
        duration_unit: 't',
        symbol: symbol
    }));

    // Store comprehensive trade data for learning
    tradeHistory.push({
        state,
        deepState,
        prediction,
        stake,
        timestamp: Date.now(),
        confidence: rawConfidence,
        smoothedConfidence: confidence,
        entropy,
        volatility,
        streak: streak.length,
        consecutiveLosses,
        modelPredictions,
        weights: adaptiveWeights,
        mode: currentMode,
        strategy: recommendedStrategy,
        consensusAgreement: consensus.agreement,
        healthScore: reasoningHealth.lastHealthScore,
        dataIntegrity: dataIntegrity.score
    });
    
    // Limit trade history size
    if (tradeHistory.length > 200) {
        tradeHistory = tradeHistory.slice(-100);
    }
};

// Event listeners
document.getElementById('connectBtn').addEventListener('click', connect);

document.getElementById('startBtn').addEventListener('click', () => {
    isBotRunning = true;
    document.getElementById('startBtn').disabled = true;
    document.getElementById('stopBtn').disabled = false;
    log('🚀 Advanced bot started with META-REASONING enabled.');
    log(`Initial LR: ${currentLearningRate.toFixed(4)}, Confidence: ${baseConfidenceThreshold.toFixed(2)}, Mode: ${currentMode}`);
    log(`Enhanced features: Bayesian Fusion, Context Memory, Meta-Q-Learning, Adaptive Thresholds`);
});

document.getElementById('stopBtn').addEventListener('click', () => {
    isBotRunning = false;
    currentContractId = null;
    isPending = false;
    consecutiveLosses = 0;
    if (ws) {
        ws.send(JSON.stringify({ forget_all: 'proposal_open_contract' }));
    }
    document.getElementById('startBtn').disabled = false;
    document.getElementById('stopBtn').disabled = true;
    
    // Log final statistics
    log('═══════════════════════════════════════');
    log('🛑 Bot stopped. Final META-ANALYSIS:');
    log('═══════════════════════════════════════');
    const totalTrades = wins + losses;
    if (totalTrades > 0) {
        log(`📊 Overall: Win Rate: ${(wins / totalTrades * 100).toFixed(1)}% (${wins}W/${losses}L)`);
        log(`🧠 Learning Rate: ${currentLearningRate.toFixed(4)}`);
        log(`💪 Reasoning Health: ${(reasoningHealth.lastHealthScore * 100).toFixed(0)}%`);
        log(`📈 Data Integrity: ${(dataIntegrity.score * 100).toFixed(0)}%`);
        log(`🎯 Final Mode: ${currentMode}`);
        
        // Log model performance
        log('───────────────────────────────────────');
        log('📈 Individual Model Performance:');
        Object.keys(modelPerformance).forEach(model => {
            const perf = modelPerformance[model];
            if (perf.total > 0) {
                const acc = (perf.correct / perf.total * 100).toFixed(1);
                const weight = adaptiveWeights[model] ? (adaptiveWeights[model] * 100).toFixed(0) : 'N/A';
                log(`  ${model.toUpperCase()}: ${acc}% accuracy (${perf.correct}/${perf.total}) | Weight: ${weight}%`);
            }
        });
        
        // Log context memory stats
        log('───────────────────────────────────────');
        log(`💾 Context Memory: ${contextMemory.length} situations stored`);
        log(`🧩 Pattern Memory: ${patternMemory.length} patterns learned`);
        
        // Calculate best meta-strategy
        const metaStrategies = {};
        tradeHistory.forEach(t => {
            if (t.strategy && t.profit !== undefined) {
                if (!metaStrategies[t.strategy]) metaStrategies[t.strategy] = { wins: 0, total: 0 };
                metaStrategies[t.strategy].total++;
                if (t.profit > 0) metaStrategies[t.strategy].wins++;
            }
        });
        
        if (Object.keys(metaStrategies).length > 0) {
            log('───────────────────────────────────────');
            log('🎲 Meta-Strategy Performance:');
            Object.keys(metaStrategies).forEach(strategy => {
                const stats = metaStrategies[strategy];
                const winRate = stats.total > 0 ? (stats.wins / stats.total * 100).toFixed(1) : '0.0';
                log(`  ${strategy.toUpperCase()}: ${winRate}% (${stats.wins}/${stats.total})`);
            });
        }
        
        log('═══════════════════════════════════════');
    }
});

// Initial UI update
updateUI();
updateTradeStats();