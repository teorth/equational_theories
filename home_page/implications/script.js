// Generate sample equations

const ids = [
    "explicit_conjecture_false",
    "explicit_conjecture_true",
    "explicit_proof_false",
    "explicit_proof_true",
    "implicit_conjecture_false",
    "implicit_conjecture_true",
    "implicit_proof_false",
    "implicit_proof_true",
    "unknown"
];

// Assuming arr is already defined
// const arr = [...];  // Your RLE encoded array

function decodeRLE(arr) {
    const decoded = [];
    for (let i = 0; i < arr.length; i += 2) {
	const value = arr[i];
	const count = arr[i + 1];
	decoded.push(...Array(count).fill(value));
    }
    return decoded;
}

function mapThroughLUT(decoded) {
    return decoded.map(index => ids[index]);
}

function reshape(array, rows, cols) {
    const result = [];
    for (let i = 0; i < rows; i++) {
	result.push(array.slice(i * cols, (i + 1) * cols));
    }
    return result;
}

// Decode RLE
const decoded = decodeRLE(arr);

// Map through LUT
const mapped = mapThroughLUT(decoded);

// Reshape to 2694x2694
const implications = reshape(mapped, 4694, 4694);

const GRAPHITI_BASE_URL = "https://teorth.github.io/equational_theories/graphiti/"
const FME_BASE_URL = "https://teorth.github.io/equational_theories/fme/"

const listPage = document.getElementById('listPage');
const detailPage = document.getElementById('detailPage');
const equationCommentary = document.getElementById('equationCommentary');
const equationList = document.getElementById('equationList');
const selectedEquation = document.getElementById('selectedEquation');
const selectedEquationDual = document.getElementById('selectedEquationDual');
const selectedEquationGraphitiLinks = document.getElementById('selectedEquationGraphitiLinks');
const smallestMagmaLink = document.getElementById('smallestMagmaLink');
const impliesList = document.getElementById('impliesList');
const antiImpliesList = document.getElementById('antiImpliesList');
const unknownImpliesList = document.getElementById('unknownImpliesList');
const impliedByList = document.getElementById('impliedByList');
const antiImpliedByList = document.getElementById('antiImpliedByList');
const unknownImpliedByList = document.getElementById('unknownImpliedByList');
const backButton = document.getElementById('backButton');
const showOnlyExplicitProofs = document.getElementById('showOnlyExplicitProofs');
const treatConjectedAsUnknownList = document.getElementById('treatConjectedAsUnknownList');
const treatConjectedAsUnknownDetail = document.getElementById('treatConjectedAsUnknownDetail');

let currentEquationIndex = null;

function showPage(pageId) {
    document.querySelectorAll('.page').forEach(page => page.classList.remove('active'));
    document.getElementById(pageId).classList.add('active');
}

let showEquivalences = false;
let filteredCachedItems = [];

function hideVisibility(elementId) {
    const element = document.getElementById(elementId);
    element.style.display = "none";
}
function showVisibility(elementId) {
    const element = document.getElementById(elementId);
    element.style.display = "block";
}

function filterEquations() {
    if (showEquivalences) {
        filteredCachedItems = cachedItems;
    } else {
        const seenClasses = new Set();
        filteredCachedItems = cachedItems.filter(item => {
            const eqClass = equiv.find(cls => cls.includes(item.index));
            if (!seenClasses.has(eqClass[0])) {
                seenClasses.add(eqClass[0]);
                return true;
            }
            return false;
        });
    }
}


// Pre-compute boolean flags for each status
const statusFlags = {
    explicit_conjecture_false: { explicit: true, conjecture: true, isTrue: false },
    explicit_conjecture_true: { explicit: true, conjecture: true, isTrue: true },
    explicit_proof_false: { explicit: true, conjecture: false, isTrue: false },
    explicit_proof_true: { explicit: true, conjecture: false, isTrue: true },
    implicit_conjecture_false: { explicit: false, conjecture: true, isTrue: false },
    implicit_conjecture_true: { explicit: false, conjecture: true, isTrue: true },
    implicit_proof_false: { explicit: false, conjecture: false, isTrue: false },
    implicit_proof_true: { explicit: false, conjecture: false, isTrue: true },
    unknown: { explicit: false, conjecture: false, isTrue: false }
};

function isImplies(status, onlyExplicit = false, treatConjecturedAsUnknown = false) {
    const flags = statusFlags[status];
    if (onlyExplicit && !flags.explicit) return false;
    if (treatConjecturedAsUnknown && flags.conjecture) return false;
    return flags.isTrue;
}

function isAntiImplies(status, onlyExplicit = false, treatConjecturedAsUnknown = false) {
    const flags = statusFlags[status];
    if (onlyExplicit && !flags.explicit) return false;
    if (treatConjecturedAsUnknown && flags.conjecture) return false;
    return !flags.isTrue && status !== 'unknown';
}
function isUnknown(status, treatConjecturedAsUnknown = false) {
    return status === 'unknown' || (treatConjecturedAsUnknown && status.includes('conjecture'));
}

function calculateStats(index, treatConjecturedAsUnknown = false) {
    const stats = {implies: 0, impliedBy: 0, antiImplies: 0, antiImpliedBy: 0, unknown: 0, unknownBy: 0};
    for (let i = 0; i < implications.length; i++) {
        if (i === index) continue;
        const forwardStatus = implications[index][i];
        const backwardStatus = implications[i][index];

        if (isImplies(forwardStatus, false, treatConjecturedAsUnknown)) stats.implies++;
        else if (isAntiImplies(forwardStatus, false, treatConjecturedAsUnknown)) stats.antiImplies++;
        else stats.unknown++;

        if (isImplies(backwardStatus, false, treatConjecturedAsUnknown)) stats.impliedBy++;
        else if (isAntiImplies(backwardStatus, false, treatConjecturedAsUnknown)) stats.antiImpliedBy++;
        else stats.unknownBy++;
    }
    return stats;
}

let cachedItems = [];
let cachedItemElements = [];


function initializeEquationList() {
    const treatConjecturedAsUnknown = treatConjectedAsUnknownList.checked;
    cachedItems = equations.map((eq, index) => {
        const stats = calculateStats(index, treatConjecturedAsUnknown);
        const element = document.createElement('div');
        element.className = 'equation-item';
        element.dataset.index = index;
        const isspecial = commentary[index+1] == undefined ? "" : "special"; // issue #547
        element.innerHTML = `
            <div class="equation-name ${isspecial}">${eq}</div>
            <div class="equation-stat implies">${stats.implies}</div>
            <div class="equation-stat impliedBy">${stats.impliedBy}</div>
            <div class="equation-stat antiImplies">${stats.antiImplies}</div>
            <div class="equation-stat antiImpliedBy">${stats.antiImpliedBy}</div>
            <div class="equation-stat unknown">${stats.unknown}</div>
            <div class="equation-stat unknownBy">${stats.unknownBy}</div>
        `;
        return {
	    eq,
	    index,
	    stats,
	    element,
	    statElements: {
                implies: element.querySelector('.implies'),
                impliedBy: element.querySelector('.impliedBy'),
                antiImplies: element.querySelector('.antiImplies'),
                antiImpliedBy: element.querySelector('.antiImpliedBy'),
                unknown: element.querySelector('.unknown'),
                unknownBy: element.querySelector('.unknownBy')
	    }
        };
    });

    filterEquations();

}

function updateEquationListStats() {
    const treatConjecturedAsUnknown = treatConjectedAsUnknownList.checked;
    cachedItems.forEach((item) => {
        const stats = calculateStats(item.index, treatConjecturedAsUnknown);
        item.stats = stats;
        item.statElements.implies.textContent = stats.implies;
        item.statElements.impliedBy.textContent = stats.impliedBy;
        item.statElements.antiImplies.textContent = stats.antiImplies;
        item.statElements.antiImpliedBy.textContent = stats.antiImpliedBy;
        item.statElements.unknown.textContent = stats.unknown;
        item.statElements.unknownBy.textContent = stats.unknownBy;
    });

    filterEquations();
}

function renderEquationList(sortBy = 'index', sortOrder = 'asc') {

    // Get the current URL
    let currentURL = window.location.href;
    // Update the URL without reloading the page
    history.pushState(null, '', currentURL.split("?")[0]);

    const header = equationList.querySelector('.header');

    filteredCachedItems.sort((a, b) => {
        if (sortBy === 'index') {
            return sortOrder === 'asc' ? a.index - b.index : b.index - a.index;
        }
        return sortOrder === 'asc' ? a.stats[sortBy] - b.stats[sortBy] : b.stats[sortBy] - a.stats[sortBy];
    });

    const fragment = document.createDocumentFragment();
    filteredCachedItems.forEach(item => fragment.appendChild(item.element));

    equationList.innerHTML = '';
    equationList.appendChild(header);
    equationList.appendChild(fragment);
}

// Call this function once when the page loads
initializeEquationList();


function renderImplications(index) {
    // Get the current URL
    let currentURL = window.location.href;

    // Check if there's already a query string
    if (currentURL.indexOf('?') > -1) {
	    currentURL = currentURL.split('?')[0] + '?' + (index+1);
    } else {
	    currentURL += '?' + (index+1);
    }


    // Update the URL without reloading the page
    history.pushState(null, '', currentURL);

    if (index === null || index < 0 || index >= equations.length) {
        console.error('Invalid equation index:', index);
        return;
    }

    currentEquationIndex = index;
    selectedEquation.textContent = equations[index];
    selectedEquation.dataset.index = index;

    if (commentary[index+1] === undefined) {
        hideVisibility("equationCommentary")
        equationCommentary.innerHTML = "";
    } else {
        showVisibility("equationCommentary")
        equationCommentary.innerHTML = commentary[index+1];
    }


    function findDual(index, duals) {
	    for (let pair of duals) {
	        if (pair[0] === index) return pair[1];
	        if (pair[1] === index) return pair[0];
	    }
	    return null; // Return null if no dual is found
    }

    // Usage:
    let dualIndex = findDual(index+1, duals);
    if (dualIndex !== null) {
	    selectedEquationDual.innerHTML = "(Dual equation: <a class='link' onclick='renderImplications("+(dualIndex-1)+");'>" + equations[dualIndex-1] + "</a>)";
    } else {
	    selectedEquationDual.innerHTML = "";
    }

    // Add this section to display equivalent equations
    const equivalentClass = equiv.find(cls => cls.includes(index)) || [index];
    const equivalentEquations = equivalentClass
          .filter(eqIndex => eqIndex !== index)
          .map(eqIndex => equations[eqIndex]);

    const equivalentEquationsHtml = equivalentEquations.length > 0
          ? `<h3>Equivalent Equations:</h3><ul>${equivalentEquations.map(eq => `<li>${eq}</li>`).join('')}</ul>`
          : '';

    // Add this line to insert the equivalent equations HTML
    document.getElementById('equivalentEquations').innerHTML = equivalentEquationsHtml;


    const onlyExplicit = showOnlyExplicitProofs.checked;
    const treatConjecturedAsUnknown = treatConjectedAsUnknownDetail.checked;

    const implies = [];
    const antiImplies = [];
    const unknownImplies = [];
    const unknownImpliesEqNum = [];
    const impliedBy = [];
    const antiImpliedBy = [];
    const unknownImpliedBy = [];
    const unknownImpliedByEqNum = [];

    let seenClasses = new Set();
    implications.forEach((row, i) => {
	if (i === index) return; // Skip self-implication

	const eqClass = equiv.find(cls => cls.includes(i));
	if (eqClass.includes(index) && !showEquivalences) return;
	if (seenClasses.has(eqClass[0]) && !showEquivalences) return;

	seenClasses.add(eqClass[0]);
	let more_same = !showEquivalences && eqClass.length > 1 ? ` (+ ${eqClass.length-1} equiv.)` : "";

	const eq = equations[i];
	const isspecial = commentary[i+1] == undefined ? "" : "special"; // issue #547

	const forwardStatus = row[index];
	const backwardStatus = implications[index][i];

	    [forwardStatus, backwardStatus].forEach((status, statusIndex) => {
            const isConjectured = status.includes('conjecture');
	        let maybe_prove;
            let forward = statusIndex == 1 ?  index : i;
            let backward = statusIndex == 1 ?  i : index;
            if (isUnknown(status, false)) {
	            let proofhref = gen_proof_url(forward, backward);
                maybe_prove = ` <a href='${proofhref}'>Prove This!</a>`;
            } else if (isUnknown(status, true)) { // conjectured
	            let proofhref = gen_proof_url(forward, backward, isImplies(status, false, false) ? "yes" : "no");
                maybe_prove = ` <a href='${proofhref}'>Prove This!</a>`;
            } else {
                var does_implies = isImplies(status, false, false);
                let proofhref;
                proofhref = gen_proof_url(forward, backward, does_implies ? "yes" : "no");
                maybe_prove = ` <a href='${proofhref}'>Try This!</a>`;
            }
            const item = `<div uid=${i} class="implication-item ${isspecial} ${status} ${isConjectured ? 'conjectured' : ''}">${eq}${more_same}${maybe_prove}</div>`;

            if (isImplies(status, onlyExplicit, treatConjecturedAsUnknown)) {
		        statusIndex === 0 ? impliedBy.push(item) : implies.push(item);
            } else if (isAntiImplies(status, onlyExplicit, treatConjecturedAsUnknown)) {
		        statusIndex === 0 ? antiImpliedBy.push(item) : antiImplies.push(item);
            } else if (isUnknown(status, treatConjecturedAsUnknown)) {
		        statusIndex === 0 ? unknownImpliedBy.push(item) : unknownImplies.push(item);
		        statusIndex === 0 ? unknownImpliedByEqNum.push(i) : unknownImpliesEqNum.push(i);
            }
	    });
    });

  selectedEquationGraphitiLinks.innerHTML = `<br>(Visualize <a target="_blank" href="${GRAPHITI_BASE_URL}?render=true&implies=${index+1}&highlight_red=${index+1}">implies</a> and <a target="_blank" href="${GRAPHITI_BASE_URL}?render=true&implied_by=${index+1}&highlight_red=${index+1}">implied by</a> of the equation)`
  if (unknownImpliesEqNum.length > 0) {
    const implies = unknownImpliesEqNum.map(x => x + 1)
    selectedEquationGraphitiLinks.innerHTML += `<br />(Visualize <a target="_blank" href="${GRAPHITI_BASE_URL}?render=true&implies=${index+1},${implies.join(",")}&highlight_red=${index+1}&highlight_blue=${implies.join(",")}&show_unknowns_conjectures=on">implies</a> and <a target="_blank" href="${GRAPHITI_BASE_URL}?render=true&implied_by=${index+1},${implies.join(",")}&highlight_red=${index+1}&highlight_blue=${implies.join(",")}&show_unknowns_conjectures=on">implied by</a> of the equation+unknowns+conjectures</a>)`
  }
  if (unknownImpliedByEqNum.length > 0) {
    const impliedby = unknownImpliedByEqNum.map(x => x + 1)
    selectedEquationGraphitiLinks.innerHTML += `<br />(Visualize <a target="_blank" href="${GRAPHITI_BASE_URL}?render=true&implies=${index+1},${impliedby.join(",")}&highlight_red=${index+1}&highlight_blue=${impliedby.join(",")}&show_unknowns_conjectures=on">implies</a> and <a target="_blank" href="${GRAPHITI_BASE_URL}?render=true&implied_by=${index+1},${impliedby.join(",")}&highlight_red=${index+1}&highlight_blue=${impliedby.join(",")}&show_unknowns_conjectures=on">implied by</a> of the equation+unknown bys+conjectured bys</a>)`
  }

  smallest_magma = smallest_magma_data[index+1]
  smallestMagmaLink.innerHTML = smallest_magma 
    ? `<br />(Size of smallest non-trivial magma: ${smallest_magma.length} <a target="_blank" href="${FME_BASE_URL}?magma=${encodeURIComponent(JSON.stringify(smallest_magma))}">(Explore)</a>)`
    : `<br />(Size of smallest non-trivial magma: N/A)`


    impliesList.innerHTML = implies.join('') || 'None';
    antiImpliesList.innerHTML = antiImplies.join('') || 'None';
    unknownImpliesList.innerHTML = unknownImplies.join('') || 'None';
    impliedByList.innerHTML = impliedBy.join('') || 'None';
    antiImpliedByList.innerHTML = antiImpliedBy.join('') || 'None';
    unknownImpliedByList.innerHTML = unknownImpliedBy.join('') || 'None';

    // Add click event listeners to all implication items
    document.querySelectorAll('.implication-item').forEach(item => {
        item.addEventListener('click', (e) => {
            const clickedIndex = parseInt(e.target.attributes['uid'].value);
            renderImplications(clickedIndex);
            showPage('detailPage');
            window.scrollTo(0, 0);  // Scroll to the top of the page
        });
    });

}

equationList.addEventListener('click', (e) => {
    if (e.target.closest('.equation-item:not(.header)')) {
        const index = parseInt(e.target.closest('.equation-item').dataset.index);
        renderImplications(index);
        showPage('detailPage');
    } else if (e.target.classList.contains('equation-stat') || e.target.classList.contains('equation-name')) {
        const sortBy = e.target.dataset.sort;
        const currentOrder = e.target.dataset.order || 'asc';
        const newOrder = currentOrder === 'asc' ? 'desc' : 'asc';
        e.target.dataset.order = newOrder;
        renderEquationList(sortBy, newOrder);
    }
});

const showEquivalencesCheckbox = document.getElementById('showEquivalences');
showEquivalencesCheckbox.addEventListener('change', () => {
    showEquivalencesCheckbox2.checked = showEquivalences;
    showEquivalences = !showEquivalencesCheckbox.checked;
    filterEquations();
    renderEquationList();
});

const showEquivalencesCheckbox2 = document.getElementById('showEquivalences2');
showEquivalencesCheckbox2.addEventListener('change', () => {
    showEquivalencesCheckbox.checked = showEquivalences;
    showEquivalences = !showEquivalencesCheckbox.checked;
    filterEquations();
    renderImplications(currentEquationIndex);
});

backButton.addEventListener('click', () => {
    showPage('listPage');
    renderEquationList(); // Re-sort by equation number when returning to list
});


// Modify the event listener for the checkbox
showOnlyExplicitProofs.addEventListener('change', () => {
    if (currentEquationIndex !== null) {
        renderImplications(currentEquationIndex);
    }
});

treatConjectedAsUnknownDetail.addEventListener('change', () => {
    if (currentEquationIndex !== null) {
        renderImplications(currentEquationIndex);
    }
});

// Modify the event listener for the checkbox
treatConjectedAsUnknownList.addEventListener('change', () => {
    updateEquationListStats();
    renderEquationList();
});


let currentURL = window.location.href;
if (currentURL.indexOf('?') > -1) {
    renderImplications(currentURL.split('?')[1]-1);
    showPage('detailPage');
} else {
    renderEquationList();
}


// Function to handle URL changes (including back/forward navigation)
function handleUrlChange() {
    let currentURL = window.location.href;
    if (currentURL.indexOf('?') > -1) {
        renderImplications(currentURL.split('?')[1]-1);
        showPage('detailPage');
    } else {
	renderEquationList();
        showPage('listPage');
    }
}

window.addEventListener('popstate', handleUrlChange);


document.addEventListener('DOMContentLoaded', function() {
    const timestamp = last_updated.timestamp * 1000; // Convert to milliseconds
    const commitHash = last_updated.commit_hash;
    
    const localDate = new Date(timestamp);
    document.getElementById('lastUpdated').textContent = localDate.toLocaleString();
    
    const commitLink = document.getElementById('commitLink');
    commitLink.href = `https://github.com/teorth/equational_theories/tree/${commitHash}`;
    commitLink.textContent = commitHash.substring(0, 7); // Display first 7 characters of the hash
});
