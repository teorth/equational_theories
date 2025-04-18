/*
A small js widget to display a magnified implication graph.

Usage:
```
<script>
  progresswidget({
    container: 'container-div-name',
    statusbar: 'statusbar-div-name',
    small: 'outcomes-small.png',
    full: 'outcomes.png',
    eqdb: 'eqdb.json' // part of finite magma explorer
  });
</script>
```

When called, the widget installs itself into container-div-name, and
uses statusbar-div-name to display text about the selected implication.
When clicked, the widget captures the mouse and displays a magnifier.
When a pixel is selected, the widget opens a proof.
*/

function progresswidget({ container, statusbar, small, full, eqdb }) {
  let equations = null;

  fetch(eqdb)
    .then(r => r.json())
    .then(json => {
      equations = json.map(e => e.eqn);
    });

  const target = document.getElementById(container);
  const statusDiv = document.getElementById(statusbar);

  const canvas = document.createElement('canvas');
  const ctx = canvas.getContext('2d');
  target.appendChild(canvas);

  const magnifier = document.createElement('canvas');
  magnifier.width = 100;
  magnifier.height = 100;
  magnifier.className = 'magnifier';
  magnifier.style.position = 'absolute';
  magnifier.style.border = '1px solid black';
  magnifier.style.pointerEvents = 'none';
  magnifier.style.display = 'none';
  magnifier.style.zIndex = 10;
  const magCtx = magnifier.getContext('2d');
  target.appendChild(magnifier);

  const loading = document.createElement('div');
  loading.style.position = 'absolute';
  loading.style.inset = '0';
  loading.style.background = 'linear-gradient(-45deg, #ffffff, #cccccc, #ffffff)';
  loading.style.backgroundSize = '400% 400%';
  loading.style.animation = 'pulse 2s infinite';
  loading.style.zIndex = 5;
  target.appendChild(loading);

  const proofLink = document.createElement('a');
  proofLink.target = '_blank';
  proofLink.rel = 'noreferrer';

  const style = document.createElement('style');
  style.textContent = `
    @keyframes pulse {
      0% { background-position: 0% 50%; }
      50% { background-position: 100% 50%; }
      100% { background-position: 0% 50%; }
    }
  `;
  document.head.appendChild(style);

  const displayImg = new Image();
  const fullImg = new Image();
  const colorCanvas = document.createElement('canvas');
  const colorCtx = colorCanvas.getContext('2d');

  let scaleX = 1, scaleY = 1;
  let virtualX = 0, virtualY = 0;
  let rawX = 0, rawY = 0;
  let lastX = -1, lastY = -1;

  const SPEED = 0.03;
  const MAG_PIXELS = 10;
  const MAG_SIZE = 100;
  const statusBuffer = [];

  function resizeCanvas() {
    canvas.width = target.clientWidth;
    canvas.height = target.clientHeight;
    if (displayImg.complete) {
      ctx.clearRect(0, 0, canvas.width, canvas.height);
      ctx.drawImage(displayImg, 0, 0, canvas.width, canvas.height);
    }
    scaleX = fullImg.width / canvas.width;
    scaleY = fullImg.height / canvas.height;
    virtualX = canvas.width / 2;
    virtualY = canvas.height / 2;
    rawX = virtualX;
    rawY = virtualY;
  }
  window.addEventListener('resize', resizeCanvas);

  displayImg.onload = () => {
    loading.remove();
    resizeCanvas();
  };
  fullImg.onload = () => {
    colorCanvas.width = fullImg.width;
    colorCanvas.height = fullImg.height;
    colorCtx.drawImage(fullImg, 0, 0);
    const pixels = colorCtx.getImageData(0, 0, fullImg.width, fullImg.height).data;
    for (let y = 0; y < fullImg.height; y++) {
      for (let x = 0; x < fullImg.width; x++) {
        const i = (y * fullImg.width + x) * 4;
        const [r, g, b] = [pixels[i], pixels[i+1], pixels[i+2]];
        let status = 'explicit_true';
        if (r === 0 && g === 96 && b === 128) status = 'implicit_true';
        if (r === 128 && g === 0 && b === 0) status = 'implicit_false';
        if (r === 255 && g === 72 && b === 72) status = 'explicit_false';
        statusBuffer[y * fullImg.width + x] = status;
      }
    }
    displayImg.src = small;
  };

  setTimeout(() => {
    fullImg.src = full;
  }, 0);

  function getPixelStatus(x, y) {
    return statusBuffer[y * fullImg.width + x];
  }

  function clamp(v, min, max) {
    return Math.max(min, Math.min(max, v));
  }

  function updateMagnifier() {
    const snappedX = Math.floor(virtualX * scaleX);
    const snappedY = Math.floor(virtualY * scaleY);

    if (snappedX !== lastX || snappedY !== lastY) {
      lastX = snappedX;
      lastY = snappedY;

      const status = getPixelStatus(snappedX, snappedY);
      const eqnX = `[${snappedX + 1}] ${equations[snappedX]}`;
      const eqnY = `${equations[snappedY]} [${snappedY + 1}]`;

      statusDiv.textContent = "";
      proofLink.href = `https://teorth.github.io/equational_theories/implications/show_proof.html?pair=${snappedX + 1},${snappedY + 1}`;
      if (status === 'implicit_true') {
        statusDiv.append(`${eqnX} ⇒ ${eqnY} - `);
        proofLink.textContent = 'proof';
        statusDiv.appendChild(proofLink);
      }
      else if (status === 'explicit_true') {
        statusDiv.append(`${eqnX} ⇒ ${eqnY} - `);
        proofLink.textContent = 'explicit proof';
        statusDiv.appendChild(proofLink);
      }
      else if (status === 'implicit_false') {
        statusDiv.append(`${eqnX} ⇏ ${eqnY} - `);
        proofLink.textContent = 'countermodel';
        statusDiv.appendChild(proofLink);
      }
      else if (status === 'explicit_false') {
        statusDiv.append(`${eqnX} ⇏ ${eqnY} - `);
        proofLink.textContent = 'explicit countermodel';
        statusDiv.appendChild(proofLink);
      }
      else {
        statusDiv.textContent = `Select an equation below.`;
      }
    }

    magCtx.clearRect(0, 0, MAG_SIZE, MAG_SIZE);
    magCtx.imageSmoothingEnabled = false;
    magCtx.drawImage(
      fullImg,
      snappedX - MAG_PIXELS / 2,
      snappedY - MAG_PIXELS / 2,
      MAG_PIXELS,
      MAG_PIXELS,
      0,
      0,
      MAG_SIZE,
      MAG_SIZE
    );

    const psize = MAG_SIZE / MAG_PIXELS;
    const center = Math.floor(MAG_PIXELS / 2);
    const cross = center * psize + psize / 2;

    magCtx.strokeStyle = 'black';
    magCtx.lineWidth = 1;
    magCtx.beginPath();
    magCtx.moveTo(cross + 0.5, 0);
    magCtx.lineTo(cross + 0.5, MAG_SIZE);
    magCtx.moveTo(0, cross + 0.5);
    magCtx.lineTo(MAG_SIZE, cross + 0.5);
    magCtx.stroke();

    magnifier.style.left = `${virtualX - MAG_SIZE / 2}px`;
    magnifier.style.top = `${virtualY - MAG_SIZE / 2}px`;
  }

  target.addEventListener('click', (e) => {
    if (!equations) return;

    const rect = canvas.getBoundingClientRect();
    if (document.pointerLockElement !== canvas) {
      rawX = e.clientX - rect.left;
      rawY = e.clientY - rect.top;
      rawX = clamp(rawX, 0, canvas.width);
      rawY = clamp(rawY, 0, canvas.height);
      virtualX = rawX;
      virtualY = rawY;
      canvas.requestPointerLock();
    } else {
      document.exitPointerLock();
    }
  });

  document.addEventListener('pointerlockchange', () => {
    if (document.pointerLockElement === canvas) {
      // open magnifier only if pointer was successfully captured
      magnifier.style.display = 'block';
      updateMagnifier();
    } else {
      magnifier.style.display = 'none';
    }
  });

  document.addEventListener('mousemove', (e) => {
    if (document.pointerLockElement !== canvas) return;
    rawX = clamp(rawX + e.movementX * SPEED, 0, canvas.width);
    rawY = clamp(rawY + e.movementY * SPEED, 0, canvas.height);
    virtualX = rawX;
    virtualY = rawY;
    updateMagnifier();
  });
}

