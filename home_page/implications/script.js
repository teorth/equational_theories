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

const EXPLICIT_CONJECTURE_FALSE = 0;
const EXPLICIT_CONJECTURE_TRUE = 1;
const EXPLICIT_PROOF_FALSE = 2;
const EXPLICIT_PROOF_TRUE = 3;
const IMPLICIT_CONJECTURE_FALSE = 4;
const IMPLICIT_CONJECTURE_TRUE = 5;
const IMPLICIT_PROOF_FALSE = 6;
const IMPLICIT_PROOF_TRUE = 7;
const UNKNOWN = 8;

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
const showFiniteGraphList = document.getElementById('showFiniteGraphList');
const showFiniteGraphDetail = document.getElementById('showFiniteGraphDetail');
const hideFullySolvedCheckbox = document.getElementById('hideFullySolved');

let currentEquationIndex = null;

let showEquivalences = false;
let filteredCachedItems = [];

let isFiniteGraph = false;
let cachedItems = [];
let cachedItemElements = [];

let arr = [];
let equiv = [];

let decoded = [];
let implications = [];

function decodeRLE(arr) {
    const decoded = [];
    for (let i = 0; i < arr.length; i += 2) {
        const value = arr[i];
        const count = arr[i + 1];
        decoded.push(...Array(count).fill(value));
    }
    return decoded;
}

function reshape(array, rows, cols) {
    const result = [];
    for (let i = 0; i < rows; i++) {
        result.push(array.slice(i * cols, (i + 1) * cols));
    }
    return result;
}

function downloadEquationListCSV() {
    showDownloadPopup();
    const rows = Array.from(equationList.children);
    const csv = "\uFEFF" + rows.map((row) => (
        Array.from(row.children).map(
            (element) => element.textContent
        ).join(",")))
        .join("\n");

    const filename = 'export_explorer_' + new Date().toLocaleDateString() + '.csv';
    downloadStringAsCSV(csv, filename);
}

function downloadRawImplicationsCSV() {
    const text_to_number=[-2, 2, -4, 4, -1, 1, -3, 3, 0];
    showDownloadPopup();
    const csv = implications.map(
        (equation) => equation.map(
            (status) => text_to_number[status]
        ).join(",")
    ).join("\n")
    downloadStringAsCSV(csv, 'export_raw_implications_' + new Date().toLocaleDateString() + '.csv');
}

function downloadStringAsCSV(string, filename) {
        // Export code gathered from https://stackoverflow.com/a/56370447/7059087
        var link = document.createElement('a');
        link.style.display = 'none';
        link.setAttribute('target', '_blank');
        link.setAttribute('href', 'data:text/csv;charset=utf-8,' + encodeURIComponent(string));
        link.setAttribute('download', filename);
        document.body.appendChild(link);
        link.click();
        document.body.removeChild(link);
}

function showPage(pageId) {
    document.querySelectorAll('.page').forEach(page => page.classList.remove('active'));
    document.getElementById(pageId).classList.add('active');
}

function hideVisibility(elementId) {
    const element = document.getElementById(elementId);
    element.style.display = "none";
}
function showVisibility(elementId) {
    const element = document.getElementById(elementId);
    element.style.display = "block";
}

function filterEquations() {
    // First filter by whether to collapse by equivalence class
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

    if (hideFullySolvedCheckbox.checked) {
        // Further filter by whether they are fully solved (e.g. they have any unknowns/conjectures remaining.)
        filteredCachedItems = filteredCachedItems.filter(item => {
            return item.stats.unknown != 0 || item.stats.unknownBy != 0
        });
    }
}


// Pre-compute boolean flags for each status
const statusFlags = [
    { explicit: true, conjecture: true, isTrue: false },
    { explicit: true, conjecture: true, isTrue: true },
    { explicit: true, conjecture: false, isTrue: false },
    { explicit: true, conjecture: false, isTrue: true },
    { explicit: false, conjecture: true, isTrue: false },
    { explicit: false, conjecture: true, isTrue: true },
    { explicit: false, conjecture: false, isTrue: false },
    { explicit: false, conjecture: false, isTrue: true },
    { explicit: false, conjecture: false, isTrue: false }
];

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
    return !flags.isTrue && status != UNKNOWN;
}
function isUnknown(status, treatConjecturedAsUnknown = false) {
    const flags = statusFlags[status];
    return status == UNKNOWN || (treatConjecturedAsUnknown && flags.conjecture);
}

function calculateStats(treatConjecturedAsUnknown = false) {
    let sccStats = []
    for (let i = 0; i < equiv.length; i++) {
        let stats = {implies: 0, impliedBy: 0, antiImplies: 0, antiImpliedBy: 0, unknown: 0, unknownBy: 0};
        for (let j = 0; j < equiv.length; j++) {
            let adjustment = 0;
            if (i == j) {
                adjustment = 1;
            }

            const forwardStatus = implications[equiv[i][0]][equiv[j][0]];
            const backwardStatus = implications[equiv[j][0]][equiv[i][0]];

            if (isImplies(forwardStatus, false, treatConjecturedAsUnknown)) stats.implies += equiv[j].length - adjustment;
            else if (isAntiImplies(forwardStatus, false, treatConjecturedAsUnknown)) stats.antiImplies += equiv[j].length - adjustment;
            else stats.unknown += equiv[j].length - adjustment;

            if (isImplies(backwardStatus, false, treatConjecturedAsUnknown)) stats.impliedBy += equiv[j].length - adjustment;
            else if (isAntiImplies(backwardStatus, false, treatConjecturedAsUnknown)) stats.antiImpliedBy += equiv[j].length - adjustment;
            else stats.unknownBy += equiv[j].length - adjustment;
        }
        sccStats.push(stats)
    }

    let overallStats = []
    for (let i = 0; i < equiv.length; i++) {
        for (const subidx of equiv[i]) {
            overallStats[subidx] = sccStats[i]
        }
    }

    return overallStats
}

function initializeEquationList() {
    const treatConjecturedAsUnknown = treatConjectedAsUnknownList.checked;
    const overallStats = calculateStats(treatConjecturedAsUnknown)
    cachedItems = equations.map((eq, index) => {
        const stats = overallStats[index];
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
    const overallStats = calculateStats(treatConjecturedAsUnknown)
    cachedItems.forEach((item) => {
        const stats = overallStats[item.index];
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

function updateUrl(queryString) {
    queries = []
    if (queryString !== undefined) {
        queries.push(String(queryString));
    }
    if (isFiniteGraph) {
        queries.push("finite");
    }

    let nextUrl = window.location.href.split("?")[0];
    if (queries.length > 0) {
        nextUrl += "?" + queries.join("&");
    }
    history.pushState(null, '', nextUrl);
}

function renderEquationList(sortBy = 'index', sortOrder = 'asc') {
    updateUrl(undefined);

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


function renderImplications(index) {
    if (index === null || index === undefined) {
        console.error('Invalid equation index:', index);
        return;
    }

    let bigIndex;
    try {
        bigIndex = toBigIntSafe(index);
    } catch (err) {
        console.error('Unable to coerce equation index to BigInt:', index, err);
        return;
    }

    if (bigIndex < 0n) {
        console.error('Invalid equation index (negative):', bigIndex.toString());
        return;
    }

    // Hide commentary by default
    hideVisibility("equationCommentary");
    equationCommentary.innerHTML = "";

    const eqId = bigIndex + 1n;
    const eq = Equation.fromId(eqId);
    updateUrl(eqId);

    currentEquationIndex = bigIndex;
    selectedEquation.textContent = `Equation${eqId.toString()}[${eq.toString()}]`;
    selectedEquation.dataset.index = bigIndex.toString();

    const dualEq = eq.dual();
    const dualIndex = dualEq.id;
    const dualDisplay = (dualIndex - 1n).toString();
    selectedEquationDual.innerHTML = `(Dual equation: <a class='link' onclick="renderImplications('${dualDisplay}')">Equation${dualIndex.toString()}[${dualEq}]</a>)`;

    if (commentary[eqId] !== undefined) {
        showVisibility("equationCommentary");
        equationCommentary.innerHTML = commentary[eqId];
    } else if(commentary[dualIndex] !== undefined) {
        showVisibility("equationCommentary");
        equationCommentary.innerHTML = `<h2>Commentary of the dual Equation${dualIndex}[${dualEq}]:</h2> ${commentary[dualIndex]}`;
    }

    if (bigIndex > BigInt(equations.length - 1)) {
        document.querySelectorAll('.implication-box').forEach(el => {
            el.style.display = 'none';
        });
        document.querySelectorAll('.checkbox-container').forEach(el => {
            el.style.display = 'none';
        });
        hideVisibility("selectedEquationGraphitiLinks");
        hideVisibility("smallestMagmaLink");

        const unavailableMessage = 'Data not available for this equation within the current explorer dataset.';
        impliesList.innerHTML = unavailableMessage;
        antiImpliesList.innerHTML = unavailableMessage;
        unknownImpliesList.innerHTML = unavailableMessage;
        impliedByList.innerHTML = unavailableMessage;
        antiImpliedByList.innerHTML = unavailableMessage;
        unknownImpliedByList.innerHTML = unavailableMessage;
        document.getElementById('equivalentEquations').innerHTML = '';

        selectedEquationGraphitiLinks.innerHTML = `<br />(Explorer data unavailable for Equation ${eqId.toString()}.)`;
        smallestMagmaLink.innerHTML = `<br />(Size of smallest non-trivial magma: N/A)`;
        return;
    }

    const indexNumber = Number(bigIndex);

    document.querySelectorAll('.implication-box').forEach(el => {
        el.style.display = 'block';
    });
    document.querySelectorAll('.checkbox-container').forEach(el => {
        el.style.display = 'block';
    });
    showVisibility("selectedEquationGraphitiLinks");
    showVisibility("smallestMagmaLink");

    // Add this section to display equivalent equations
    const equivalentClass = equiv.find(cls => cls.includes(indexNumber)) || [indexNumber];
    const equivalentEquations = equivalentClass
        .filter(eqIndex => eqIndex !== indexNumber)
        .map(eqIndex => equations[eqIndex]);

    const equivalentEquationsHtml = equivalentEquations.length > 0
        ? `<h3>Equivalent Equations:</h3><ul>${equivalentEquations.map(eqStr => `<li>${eqStr}</li>`).join('')}</ul>`
        : '';

    // Add this line to insert the equivalent equations HTML
    document.getElementById('equivalentEquations').innerHTML = equivalentEquationsHtml;

    const baseEquivalentEquationId = equivalentClass[0];
    const dualEquivalentClass = equiv.find(cls => cls.includes(Number(dualIndex - 1n))) || [Number(dualIndex - 1n)];
    const baseDualEquivalentEquationId = dualEquivalentClass[0];
    if (commentary[eqId] === undefined && commentary[dualIndex] === undefined && commentary[baseEquivalentEquationId + 1] !== undefined) {
        showVisibility("equationCommentary");
        equationCommentary.innerHTML = `
            <h2>Commentary of the equivalent ${equations[baseEquivalentEquationId]}:</h2><br>
            ${commentary[baseEquivalentEquationId + 1]}
        `;
    } else if (commentary[eqId] === undefined && commentary[dualIndex] === undefined && commentary[baseDualEquivalentEquationId + 1] !== undefined) {
        showVisibility("equationCommentary");
        equationCommentary.innerHTML = `
            <h2>Commentary of ${equations[baseDualEquivalentEquationId]} which is equivalent to the dual Equation${dualIndex}[${dualEq}]:</h2><br>
            ${commentary[baseDualEquivalentEquationId + 1]}
        `;
    }

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

    const seenClasses = new Set();
    implications.forEach((row, i) => {
        if (i === indexNumber) return;  // Skip self-implication

        const eqClass = equiv.find(cls => cls.includes(i));
        if (eqClass.includes(indexNumber) && !showEquivalences) return;
        if (seenClasses.has(eqClass[0]) && !showEquivalences) return;

        seenClasses.add(eqClass[0]);
        const moreSame = !showEquivalences && eqClass.length > 1 ? ` (+ ${eqClass.length - 1} equiv.)` : "";

        const eqText = equations[i];
        const isSpecial = commentary[i + 1] == undefined ? "" : "special"; // issue #547

        const forwardStatus = row[indexNumber];
        const backwardStatus = implications[indexNumber][i];

        [forwardStatus, backwardStatus].forEach((status, statusIndex) => {
            const isConjectured = statusFlags[status].conjecture;
            let maybeProve;
            const forward = statusIndex === 1 ? indexNumber : i;
            const backward = statusIndex === 1 ? i : indexNumber;
            const finite = isFiniteGraph ? "&finite" : "";

            if (isUnknown(status, false)) {
                const proofHref = gen_proof_url(forward, backward);
                maybeProve = ` <a href='${proofHref}'>Prove This!</a>`;
            } else if (isUnknown(status, true)) { // conjectured
                const proofHref = gen_proof_url(forward, backward, isImplies(status, false, false) ? "yes" : "no");
                maybeProve = ` <a href='${proofHref}'>Prove This!</a> <a href="show_proof.html?pair=${forward + 1},${backward + 1}${finite}" target="_blank">Show Proof</a>`;
            } else {
                const doesImplies = isImplies(status, false, false);
                const proofHref = gen_proof_url(forward, backward, doesImplies ? "yes" : "no");
                maybeProve = ` <a href='${proofHref}'>Try This!</a> <a href="show_proof.html?pair=${forward + 1},${backward + 1}${finite}" target="_blank">Show Proof</a>`;
            }

            const item = `<div uid=${i} class="implication-item ${isSpecial} ${ids[status]} ${isConjectured ? 'conjectured' : ''}">${eqText}${moreSame}${maybeProve}</div>`;

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

    const eqIdString = eqId.toString();
    let graphiti_url = `${GRAPHITI_BASE_URL}?render=true&highlight_red=${eqIdString}`;
    if (isFiniteGraph) {
        graphiti_url += "&show_finite_graph=on";
    }
    selectedEquationGraphitiLinks.innerHTML = `<br>(Visualize <a target="_blank" href="${graphiti_url}&implies=${eqIdString}">implies</a> and <a target="_blank" href="${graphiti_url}&implied_by=${eqIdString}">implied by</a> of the equation, or see <a target="_blank" href="${graphiti_url}&neighborhood_of=${eqIdString}&neighborhood_of_distance=1">1</a>, <a target="_blank" href="${graphiti_url}&neighborhood_of=${eqIdString}&neighborhood_of_distance=2">2</a>, <a target="_blank" href="${graphiti_url}&neighborhood_of=${eqIdString}&neighborhood_of_distance=3">3</a> graph edges away)`;
    if (unknownImpliesEqNum.length > 0) {
        const impliesIds = unknownImpliesEqNum.map(x => x + 1);
        selectedEquationGraphitiLinks.innerHTML += `<br />(Visualize <a target="_blank" href="${graphiti_url}&implies=${eqIdString},${impliesIds.join(",")}&highlight_blue=${impliesIds.join(",")}&show_unknowns_conjectures=on">implies</a> and <a target="_blank" href="${graphiti_url}&implied_by=${eqIdString},${impliesIds.join(",")}&highlight_blue=${impliesIds.join(",")}&show_unknowns_conjectures=on">implied by</a> of the equation+unknowns+conjectures</a>)`;
    }
    if (unknownImpliedByEqNum.length > 0) {
        const impliedByIds = unknownImpliedByEqNum.map(x => x + 1);
        selectedEquationGraphitiLinks.innerHTML += `<br />(Visualize <a target="_blank" href="${graphiti_url}&implies=${eqIdString},${impliedByIds.join(",")}&highlight_blue=${impliedByIds.join(",")}&show_unknowns_conjectures=on">implies</a> and <a target="_blank" href="${graphiti_url}&implied_by=${eqIdString},${impliedByIds.join(",")}&highlight_blue=${impliedByIds.join(",")}&show_unknowns_conjectures=on">implied by</a> of the equation+unknown bys+conjectured bys</a>)`;
    }

    const smallestMagma = smallest_magma_data[indexNumber + 1];
    smallestMagmaLink.innerHTML = smallestMagma
        ? `<br />(Size of smallest non-trivial magma: ${smallestMagma.length} <a target="_blank" href="${FME_BASE_URL}?magma=${encodeURIComponent(JSON.stringify(smallestMagma))}">(Explore)</a>)`
        : `<br />(Size of smallest non-trivial magma: N/A)`;

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
            window.scrollTo(0, 0); // Scroll to the top of the page
        });
    });
}

function urlParams() {
    function isNumber(str) {
        return /^[+-]?(\d+(\.\d*)?|\.\d+)$/.test(str);
    }

    const params = Object.fromEntries(
        new URLSearchParams(window.location.search).entries(),
    );

    if (params == {}) return {};
    for (p of Object.keys(params)) {
        if (isNumber(p) ) {
            params.equation = p;
        }
    }

    return params;
}

function loadGraphAndRender(jsondata) {
    arr = jsondata["rle_encoded_array"]
    equiv = jsondata["equivalence_classes"]

    // Decode RLE
    decoded = decodeRLE(arr);

    // Reshape to 4694x4694
    implications = reshape(decoded, 4694, 4694);

    let params = urlParams();
    if (params.equation) {
        renderImplications(params.equation - 1);
        showPage('detailPage');
        requestIdleCallback(() => {
            initializeEquationList();
        })
    } else {
        initializeEquationList();
        renderEquationList();
    }
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
    treatConjectedAsUnknownList.checked = treatConjectedAsUnknownDetail.checked;
    updateEquationListStats();
    if (currentEquationIndex !== null) {
        renderImplications(currentEquationIndex);
    }
});

treatConjectedAsUnknownList.addEventListener('change', () => {
    treatConjectedAsUnknownDetail.checked = treatConjectedAsUnknownList.checked;
    updateEquationListStats();
    renderEquationList();
});

function loadAndDisplayGraph(file) {
    return fetch(file)
        .then(async (response) => {
            if (!response.ok) {
                //console.error(`HTTP error! Status: ${response.status}`);
                throw(`HTTP error! Status: ${response.status}`);
            }

            const jsondata = await response.json();

            loadGraphAndRender(jsondata)
        })
}

function toggleFinite(is_finite) {
    if (is_finite) {
        document.getElementById("finiteGreenBand").style.display = "block";
        isFiniteGraph = true;
    } else {
        document.getElementById("finiteGreenBand").style.display = "none";
        isFiniteGraph = false;
    }
    showFiniteGraphList.checked = showFiniteGraphDetail.checked = isFiniteGraph;
}

showFiniteGraphDetail.addEventListener('change', () => {
    toggleFinite(showFiniteGraphDetail.checked)
    let graph_file = showFiniteGraphDetail.checked ? "finite_graph.json" : "graph.json";
    loadAndDisplayGraph(graph_file).catch((e) => {
        alert(e);
        showFiniteGraphList.checked ^= 1;
        showFiniteGraphDetail.checked ^= 1;
        toggleFinite(showFiniteGraphDetail.checked)
    });
});

showFiniteGraphList.addEventListener('change', () => {
    toggleFinite(showFiniteGraphList.checked)
    let graph_file = showFiniteGraphDetail.checked ? "finite_graph.json" : "graph.json";
    loadAndDisplayGraph(graph_file).catch((e) => {
        alert(e);
        showFiniteGraphList.checked ^= 1;
        showFiniteGraphDetail.checked ^= 1;
        toggleFinite(showFiniteGraphDetail.checked)
    });
});

hideFullySolvedCheckbox.addEventListener('change', () => {
    filterEquations();
    renderEquationList();
});

// Function to handle URL changes (including back/forward navigation)
function handleUrlChange() {
    let params = urlParams();
    if (params.equation) {
        renderImplications(params.equation-1);
        showPage('detailPage');
    } else {
        renderEquationList();
        showPage('listPage');
    }
}

window.addEventListener('popstate', handleUrlChange);

if (urlParams().finite !== undefined) {
    toggleFinite(true);
    loadAndDisplayGraph('finite_graph.json').catch((e) => alert(e));
} else {
    loadAndDisplayGraph('graph.json').catch((e) => alert(e));
}

document.addEventListener('DOMContentLoaded', function() {
    const timestamp = last_updated.timestamp * 1000; // Convert to milliseconds
    const commitHash = last_updated.commit_hash;

    const localDate = new Date(timestamp);
    document.getElementById('lastUpdated').textContent = localDate.toLocaleString();

    const commitLink = document.getElementById('commitLink');
    commitLink.href = `https://github.com/teorth/equational_theories/tree/${commitHash}`;
    commitLink.textContent = commitHash.substring(0, 7); // Display first 7 characters of the hash
});
