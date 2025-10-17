
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

const MAX_HISTORY = 100; // Increased for better pattern recognition
let currentContractId = null;
let balanceSubscriptionId = null;

// Enhanced learning parameters with adaptive decay
const baseLearningRate = 0.15;
const learningRateDecay = 0.9995;
let currentLearningRate = baseLearningRate;
const discountFactor = 0.92;
const baseConfidenceThreshold = 0.55;
const epsilon = 0.02; // Exploration rate for epsilon-greedy
const cooldownMs = 5000;
let nextTradeTime = 0;
let isPending = false;
let wins = 0;
let losses = 0;
let consecutiveLosses = 0;
const maxMartingaleLevels = 4; // Increased for better recovery
const martingaleMultiplier = 2; // Softer multiplier for risk management

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

// Enhanced: Calculate Exponential Moving Average (more responsive than SMA)
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
        const weight = Math.exp(-0.1 * (window - idx - 1)); // More weight to recent
        return sum + weight * Math.pow(tick.quote - ema, 2);
    }, 0) / window;
    return Math.sqrt(variance);
};

// Enhanced: Advanced Markov chain with higher-order transitions
const calculateMarkovProbabilities = (history) => {
    if (history.length < 3) return { oddToOdd: 0.5, oddToEven: 0.5, evenToOdd: 0.5, evenToEven: 0.5 };
    
    // First-order transitions
    let transitions = { oddToOdd: 0, oddToEven: 0, evenToOdd: 0, evenToEven: 0 };
    let counts = { odd: 0, even: 0 };
    
    // Second-order transitions (considering 2 previous states)
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

// New: Calculate entropy (randomness measure)
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
    return entropy / Math.log2(10); // Normalize to 0-1
};

// New: Detect cyclic patterns using FFT approximation
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
    
    // Calculate momentum (acceleration of streak)
    let momentum = 0;
    if (history.length >= 10) {
        const recent10 = history.slice(-10);
        const typeCount = recent10.filter(t => (t.digit % 2 === 1 ? 'odd' : 'even') === lastType).length;
        momentum = (typeCount / 10) - 0.5; // -0.5 to 0.5
    }
    
    return { length, type: lastType, momentum };
};

// New: Pattern matching with historical success
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

// New: Store successful patterns
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
    
    // Keep only top 100 patterns by weighted score
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

// Enhanced: Update Q-table with eligibility traces
const updateQTable = (state, action, reward, deepState = null) => {
    // Simple Q-table update
    qTable[state][action] = qTable[state][action] + currentLearningRate * (reward - qTable[state][action]);
    
    // Deep Q-table update
    if (deepState && deepQTable[deepState]) {
        deepQTable[deepState][action] = deepQTable[deepState][action] + 
            currentLearningRate * (reward + discountFactor * Math.max(deepQTable[deepState].odd, deepQTable[deepState].even) - deepQTable[deepState][action]);
    }
    
    // Decay learning rate
    currentLearningRate = Math.max(0.01, currentLearningRate * learningRateDecay);
    
    storage.set('qTable', JSON.stringify(qTable));
    storage.set('deepQTable', JSON.stringify(deepQTable));
    log(`Updated Q-tables (LR=${currentLearningRate.toFixed(4)}): Simple[${state}]=${qTable[state].odd.toFixed(3)}/${qTable[state].even.toFixed(3)}`);
};

// New: Update model performance tracking
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

// New: Calculate adaptive weights based on performance
const getAdaptiveWeights = () => {
    const weights = {};
    let totalAccuracy = 0;
    
    Object.keys(modelPerformance).forEach(model => {
        const perf = modelPerformance[model];
        const accuracy = perf.total > 0 ? perf.correct / perf.total : 0.5;
        weights[model] = Math.pow(accuracy, 2); // Square to amplify differences
        totalAccuracy += weights[model];
    });
    
    // Normalize
    Object.keys(weights).forEach(model => {
        weights[model] = totalAccuracy > 0 ? weights[model] / totalAccuracy : 1 / Object.keys(weights).length;
    });
    
    // Ensure minimum weight for exploration
    Object.keys(weights).forEach(model => {
        weights[model] = Math.max(0.05, weights[model]);
    });
    
    // Re-normalize after min weight adjustment
    totalAccuracy = Object.values(weights).reduce((sum, w) => sum + w, 0);
    Object.keys(weights).forEach(model => {
        weights[model] = weights[model] / totalAccuracy;
    });
    
    return weights;
};

// New: Risk-adjusted confidence threshold
const getAdaptiveConfidenceThreshold = () => {
    const totalTrades = wins + losses;
    if (totalTrades < 10) return baseConfidenceThreshold;
    
    const winRate = wins / totalTrades;
    const volatility = consecutiveLosses / Math.max(1, totalTrades / 10);
    
    // Increase threshold if losing, decrease if winning
    let adjustment = 0;
    if (winRate < 0.45) {
        adjustment = 0.1; // More cautious
    } else if (winRate > 0.60) {
        adjustment = -0.05; // More aggressive
    }
    
    adjustment += volatility * 0.05; // Add caution during volatile periods
    
    return Math.min(0.85, Math.max(0.55, baseConfidenceThreshold + adjustment));
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
            
            if (balanceSubscriptionId) {
                ws.send(JSON.stringify({ forget: balanceSubscriptionId }));
            }
            ws.send(JSON.stringify({ balance: 1, subscribe: 1 }));
            
            const symbol = document.getElementById('symbol').value;
            ws.send(JSON.stringify({ ticks: symbol, subscribe: 1 }));
            log(`Subscribed to ticks for ${symbol}.`);
            
            document.getElementById('connectBtn').disabled = true;
            document.getElementById('startBtn').disabled = false;
        } else if (msgType === 'balance') {
            document.getElementById('balance').textContent = `$${data.balance.balance}`;
        } else if (msgType === 'tick') {
            const quote = parseFloat(data.tick.quote);
            if (isNaN(quote)) {
                log('Invalid tick quote received.', 'error');
                return;
            }
            const digit = Math.floor(quote * 100) % 10;
            tickHistory.push({ ...data.tick, quote, digit });
            if (tickHistory.length > MAX_HISTORY) {
                tickHistory.shift();
            }
            updateUI();
            
            if (isBotRunning && !currentContractId && Date.now() >= nextTradeTime && !isPending) {
                setTimeout(() => analyzeAndTrade(data.tick), 100);
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
                    updateQTable(lastTrade.state, lastTrade.prediction, reward, lastTrade.deepState);
                    
                    // Update model performance
                    if (lastTrade.modelPredictions) {
                        const actual = lastTrade.prediction; // The prediction we made
                        updateModelPerformance(lastTrade.modelPredictions, actual);
                    }
                    
                    // Store pattern
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

    const recent = tickHistory.slice(-50);
    const lastDigitNum = recent[recent.length - 1].digit;
    const state = lastDigitNum % 2 === 1 ? 'odd' : 'even';

    // === Model 1: Enhanced Statistical Probability ===
    const oddCount = recent.filter(t => t.digit % 2 === 1).length;
    const evenCount = recent.length - oddCount;
    let statProbOdd = oddCount / recent.length;
    let statProbEven = evenCount / recent.length;
    
    // Apply mean reversion bias
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
    
    // Use second-order if available
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
    const volatility = calculateVolatility(recent, 20);
    const emaShort = calculateEMA(recent, 5);
    const emaLong = calculateEMA(recent, 20);
    const trendStrength = (emaShort - emaLong) / emaLong;
    const trendScore = Math.tanh(trendStrength * 10) * 0.1; // Normalize with tanh
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
    
    // Blend simple and deep Q-learning
    const blendedQOdd = (qProbOdd * 0.4 + deepQProbOdd * 0.6);
    const blendedQEven = (qProbEven * 0.4 + deepQProbEven * 0.6);

    // === Model 5: Advanced Streak Analysis ===
    const streak = calculateStreak(recent);
    let streakAdjustmentOdd = 0;
    let streakAdjustmentEven = 0;
    
    // Non-linear streak penalty with momentum
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
    const entropy = calculateEntropy(recent, 30);
    let entropyAdjustmentOdd = 0;
    let entropyAdjustmentEven = 0;
    
    // High entropy = more random, reduce confidence; Low entropy = more predictable
    if (entropy > 0.9) {
        // Very random, bet against current state (gambler's fallacy exploitation)
        entropyAdjustmentOdd = state === 'odd' ? -0.05 : 0.05;
        entropyAdjustmentEven = state === 'even' ? -0.05 : 0.05;
    } else if (entropy < 0.7) {
        // Low entropy, trend continuation more likely
        entropyAdjustmentOdd = state === 'odd' ? 0.08 : -0.08;
        entropyAdjustmentEven = state === 'even' ? 0.08 : -0.08;
    }

    // === Model 8: Cyclic Pattern Detection ===
    const cycleInfo = detectCyclicPattern(recent, 10);
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

    let finalProbOdd = (
        adaptiveWeights.stat * statProbOdd +
        adaptiveWeights.markov * markovProbOdd +
        adaptiveWeights.trend * (0.5 + trendScore + volatilityAdjustment) +
        adaptiveWeights.qlearning * blendedQOdd +
        adaptiveWeights.streak * (0.5 + streakAdjustmentOdd) +
        adaptiveWeights.pattern * patternProbOdd +
        adaptiveWeights.entropy * (0.5 + entropyAdjustmentOdd)
    );
    
    let finalProbEven = (
        adaptiveWeights.stat * statProbEven +
        adaptiveWeights.markov * markovProbEven +
        adaptiveWeights.trend * (0.5 - trendScore + volatilityAdjustment) +
        adaptiveWeights.qlearning * blendedQEven +
        adaptiveWeights.streak * (0.5 + streakAdjustmentEven) +
        adaptiveWeights.pattern * patternProbEven +
        adaptiveWeights.entropy * (0.5 + entropyAdjustmentEven)
    );

    // Add cycle influence if detected
    if (cycleInfo.hasCycle) {
        finalProbOdd = finalProbOdd * 0.85 + cycleProbOdd * 0.15;
        finalProbEven = finalProbEven * 0.85 + cycleProbEven * 0.15;
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
    let confidence = Math.max(finalProbOdd, finalProbEven);
    
    // Epsilon-greedy: Sometimes explore random actions
    if (Math.random() < epsilon) {
        prediction = Math.random() < 0.5 ? 'odd' : 'even';
        confidence = 0.5;
        log('Exploration mode: Random prediction for learning');
    } else {
        prediction = finalProbOdd > finalProbEven ? 'odd' : 'even';
    }

    if (isNaN(confidence)) {
        log('Invalid confidence. Skipping trade.', 'error');
        isPending = false;
        return;
    }

    log(`Advanced Analysis: Odds=${(finalProbOdd * 100).toFixed(1)}%, Evens=${(finalProbEven * 100).toFixed(1)}%, Conf=${(confidence * 100).toFixed(1)}%`);
    log(`Metrics: Entropy=${entropy.toFixed(2)}, Vol=${volatility.toFixed(2)}, Streak=${streak.length}(${streak.type}), Momentum=${streak.momentum.toFixed(2)}`);
    log(`Model Weights: Stat=${(adaptiveWeights.stat * 100).toFixed(0)}%, Markov=${(adaptiveWeights.markov * 100).toFixed(0)}%, Q=${(adaptiveWeights.qlearning * 100).toFixed(0)}%`);

    // === Risk Management: Adaptive Confidence Threshold ===
    const adaptiveThreshold = getAdaptiveConfidenceThreshold();
    
    if (confidence < adaptiveThreshold) {
        log(`Low confidence (${(confidence * 100).toFixed(1)}% < ${(adaptiveThreshold * 100).toFixed(1)}%). Skipping trade.`);
        isPending = false;
        return;
    }

    // === Advanced Risk Management: Multi-Factor Safety Checks ===
    
    // 1. Martingale safety circuit breaker
    if (consecutiveLosses > maxMartingaleLevels) {
        log(`Max Martingale levels (${maxMartingaleLevels}) exceeded. Risk circuit breaker activated.`);
        isPending = false;
        return;
    }

    // 2. High entropy safety (very random market)
    if (entropy > 0.95 && confidence < 0.75) {
        log('Extremely high entropy detected. Market too random - skipping for safety.');
        isPending = false;
        return;
    }

    // 3. Volatility spike protection
    if (volatility > 1.2 && confidence < 0.70) {
        log('High volatility spike detected. Requiring higher confidence - skipping.');
        isPending = false;
        return;
    }

    // 4. Consecutive losses with low confidence
    if (consecutiveLosses >= 2 && confidence < 0.68) {
        log('On losing streak. Requiring higher confidence - skipping.');
        isPending = false;
        return;
    }

    // === Sophisticated Stake Management ===
    let baseStake = parseInt(document.getElementById('stake').value);
    const balanceText = document.getElementById('balance').textContent.replace('$', '');
    const balance = parseFloat(balanceText);
    
    if (balance < baseStake * 5) {
        log('Insufficient balance for safe trading. Consider stopping.', 'error');
        isPending = false;
        return;
    }

    // Smart Martingale with decay
    const martingaleDecayFactor = Math.pow(0.95, consecutiveLosses); // Soften multiplier over time
    const currentMultiplier = Math.pow(martingaleMultiplier, consecutiveLosses) * martingaleDecayFactor;
    let stake = Math.round(baseStake * currentMultiplier);
    
    // Confidence-based stake adjustment
    const confidenceBonus = confidence > 0.75 ? 1.3 : confidence > 0.70 ? 1.15 : 1.0;
    stake = Math.round(stake * confidenceBonus);
    
    // Entropy-based adjustment (reduce stake in high entropy)
    const entropyPenalty = entropy > 0.85 ? 0.8 : 1.0;
    stake = Math.round(stake * entropyPenalty);
    
    // Kelly Criterion inspired sizing (conservative)
    const kellyFraction = (confidence - 0.5) * 2; // 0 to 1 range
    const kellyStake = Math.round(balance * kellyFraction * 0.02); // Max 2% of balance
    stake = Math.min(stake, kellyStake);
    
    // Safety caps
    stake = Math.min(stake, Math.floor(balance * 0.08)); // Max 8% of balance
    stake = Math.max(stake, baseStake); // Min is base stake
    stake = Math.min(stake, baseStake * 10); // Never more than 10x base
    
    log(`Smart Stake Calculation: Base=$${baseStake}, Martingale=${currentMultiplier.toFixed(2)}x, Confidence=${confidenceBonus.toFixed(2)}x, Kelly=$${kellyStake}, Final=$${stake}`);

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
        confidence,
        entropy,
        volatility,
        streak: streak.length,
        consecutiveLosses,
        modelPredictions,
        weights: adaptiveWeights,
        threshold: adaptiveThreshold
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
    log('Advanced bot started. Multi-model analysis active.');
    log(`Initial learning rate: ${currentLearningRate.toFixed(4)}, Confidence threshold: ${baseConfidenceThreshold.toFixed(2)}`);
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
    log('Bot stopped. Final statistics:');
    const totalTrades = wins + losses;
    if (totalTrades > 0) {
        log(`Win Rate: ${(wins / totalTrades * 100).toFixed(1)}% (${wins}W/${losses}L)`);
        log(`Learning Rate: ${currentLearningRate.toFixed(4)}`);
        
        // Log model performance
        log('Model Performance:');
        Object.keys(modelPerformance).forEach(model => {
            const perf = modelPerformance[model];
            if (perf.total > 0) {
                const acc = (perf.correct / perf.total * 100).toFixed(1);
                log(`  ${model}: ${acc}% (${perf.correct}/${perf.total})`);
            }
        });
    }
});

// Initial UI update
updateUI();
updateTradeStats();
