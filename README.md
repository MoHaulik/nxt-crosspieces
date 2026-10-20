# Crosspieces

A crossword you solve with your hands. Mixed reality for **Meta Quest 3**, in the browser, with WebXR and three.js. No build step, no image or audio files: the pieces are carved at load time as Gaussian splats, and every sound is synthesized with the Web Audio API.
A [NXT/WebXR](https://www.nxtwebxr.com) production. Live at **https://mohaulik.github.io/nxt-crosspieces/**

Built on the die Hände skeleton (session setup, passthrough rendering, the 25-joint hand rig and its depth-only occluders, the compressed HRTF audio bus, the `?sim` desktop preview).

Played with bare hands (hand tracking). Controllers work as a fallback: trigger or grip to hold.

## How it plays

1. **A crossword floats in front of you.** Dark glass tiles with hairline frames; the grid draws itself.
2. **The pieces stand on a black marble tray that curves round you.** Each is a small chess piece with something carved on top, and each one is one word. A crown is KING. A bone is DOG. A snail is SLOW.
3. **Pinch a piece to pick it up.** Turn it in your fingers to look at it.
4. **Point it at its word and let go** (or throw it). The word you are aiming at lights gold and a dotted arc shows where the piece will fly.
5. **Right:** the piece flashes green and pours itself into the grid, every Gaussian flying to a letter, and the word appears. **Wrong:** it flashes red, shakes its head, and flies back to its place. Three misses on one piece pencil in its first letter.
6. **Checkmate.** When every word is in, the grid shimmers, you get your time and misses, and the next puzzle draws itself.

Five set puzzles, named for the phases of a chess game, use all 25 pieces once, from literal (crown → KING) through associations (horseshoe → LUCK, umbrella → RAIN) to the sly ones (nose → SMELL, crystals → COLD, padlock → SAFE). After that come encores: random handfuls of pieces laid out as a new crossword each time. Progress is saved in the browser.

## How it is made

- `index.html`: the landing page (its background is the live scene), the splat renderer, the board, hands, audio, everything.
- `carver.js`: a Web Worker that carves the pieces. Each piece is a signed distance field (a Staunton pedestal plus a topper modelled from spheres, lathes, tori, capsules and smooth unions). The surface is found on a voxel grid (coarser for the pedestal, finer for the carving), every surface voxel is pulled onto the surface, and becomes a flat oriented Gaussian with its own colour, opacity, material, normal and baked occlusion. Procedural marble veins, wood rings, malachite bands, lapis with pyrite flecks, verdigris in the hollows of bronze.
- **Splat rendering:** each splat's 3D covariance is projected to a screen-space ellipse (EWA, with the 0.3 px low-pass and its opacity compensation) and drawn as a Gaussian, back to front. Pieces are depth-sorted on the CPU only when your viewpoint round them has moved enough. Unlike captured splats with baked colour, these are *lit* every frame in the vertex shader (metal, clear coat, subsurface, velvet sheen, moonstone iridescence, glass) by a studio of softboxes, so gold really reflects as you turn it.
- **Dissolve and gather** are done in the same shader: on a right answer each Gaussian picks a letter cell and flies there; new pieces materialise from a swirl.
- `assets/hand-left.glb`, `assets/hand-right.glb`: the generic WebXR hand meshes from [`@webxr-input-profiles/assets`](https://github.com/immersive-web/webxr-input-profiles) (MIT), drawn depth-only so your real fingers pass in front of the pieces.
- The crossword layout is a small randomized backtracking search: every word crosses another, no letters touch side by side, compact and a little wider than tall.
- `CFG` at the top of the script holds the layout (eye height above the tray, tray radii, board distance), grab thresholds, aim assist and how much the room is dimmed.

## Desktop preview

- `?sim`: the mouse is your hand. Hold the button over a piece to pinch it, drag up onto its word, let go.
- `?lab`: every piece on its own, drag to orbit, wheel to zoom. `?lab=crown` or `?lab=nose,moon` for just those.
- `?emu`: loads Meta's [IWER](https://github.com/meta-quest/immersive-web-emulation-runtime) and emulates a Quest 3 with tracked hands, so the real WebXR session, hand joints, pinch and target-ray code run at a desk (drive it from the console through `__X.EMU.hands.right.position` and `.updatePinchValue()`).
- `?manual`: replaces `requestAnimationFrame` with a queue you step with `__pump(n)`, for testing in a background tab.

Serve the folder over HTTPS (or `localhost`) for WebXR; GitHub Pages works as is.

Not in this version: daily puzzles, sharing, a real tabletop (the tray is virtual), analytics.
