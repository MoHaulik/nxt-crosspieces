// The carver. Runs in a worker. Every piece is a signed distance field (centimetres, y up, the foot at y = 0),
// carved into a few thousand oriented Gaussian splats: flat discs lying on the surface, each with its own colour,
// opacity, material and normal. The page lights them every frame, so the gold really reflects as you turn it in your fingers.
'use strict';
const { abs, sqrt, min, max, sin, cos, atan2, floor, ceil, PI, exp, pow, sign } = Math;
const TAU = PI * 2;
const L2 = (x, y) => sqrt(x * x + y * y), L3 = (x, y, z) => sqrt(x * x + y * y + z * z);
const cl = (x, a, b) => x < a ? a : x > b ? b : x, mix = (a, b, t) => a + (b - a) * t, mod = (a, n) => a - n * floor(a / n);
const sst = (a, b, x) => { const t = cl((x - a) / (b - a), 0, 1); return t * t * (3 - 2 * t); };
const smin = (a, b, k) => { const h = max(k - abs(a - b), 0) / k; return min(a, b) - h * h * k * .25; };
const smax = (a, b, k) => -smin(-a, -b, k);

// ── noise ──
function h3(i, j, k) { let n = Math.imul(i, 374761393) ^ Math.imul(j, 668265263) ^ Math.imul(k, 1274126177); n = Math.imul(n ^ (n >>> 13), 1274126177); return ((n ^ (n >>> 16)) >>> 0) / 4294967296; }
function vn(x, y, z) {
  const i = floor(x), j = floor(y), k = floor(z); let u = x - i, v = y - j, w = z - k; u = u * u * (3 - 2 * u); v = v * v * (3 - 2 * v); w = w * w * (3 - 2 * w);
  const a = mix(h3(i, j, k), h3(i + 1, j, k), u), b = mix(h3(i, j + 1, k), h3(i + 1, j + 1, k), u), c = mix(h3(i, j, k + 1), h3(i + 1, j, k + 1), u), d = mix(h3(i, j + 1, k + 1), h3(i + 1, j + 1, k + 1), u);
  return mix(mix(a, b, v), mix(c, d, v), w);
}
function fbm(x, y, z, o = 4) { let s = 0, a = .5; for (let i = 0; i < o; i++) { s += a * vn(x, y, z); x = x * 2.03 + 17.1; y = y * 2.03 + 3.7; z = z * 2.03 + 9.2; a *= .5; } return s / (1 - pow(.5, o)); }

// ── primitives ──
const sph = (x, y, z, r) => L3(x, y, z) - r;
function ell(x, y, z, a, b, c) { const k0 = L3(x / a, y / b, z / c), k1 = L3(x / (a * a), y / (b * b), z / (c * c)); return k1 < 1e-9 ? -min(a, b, c) : k0 * (k0 - 1) / k1; }
function box(x, y, z, a, b, c, r = 0) { const qx = abs(x) - a + r, qy = abs(y) - b + r, qz = abs(z) - c + r; return L3(max(qx, 0), max(qy, 0), max(qz, 0)) + min(max(qx, qy, qz), 0) - r; }
function box2(x, y, a, b, r = 0) { const qx = abs(x) - a + r, qy = abs(y) - b + r; return L2(max(qx, 0), max(qy, 0)) + min(max(qx, qy), 0) - r; }
function cylY(x, y, z, r, hh, rr = 0) { const dx = L2(x, z) - r + rr, dy = abs(y) - hh + rr; return min(max(dx, dy), 0) + L2(max(dx, 0), max(dy, 0)) - rr; }
const cylZ = (x, y, z, r, hh, rr = 0) => cylY(x, z, y, r, hh, rr);
const torY = (x, y, z, R, r) => L2(L2(x, z) - R, y) - r; // a ring lying flat
const torZ = (x, y, z, R, r) => L2(L2(x, y) - R, z) - r; // a ring standing up, facing you
function cap(x, y, z, ax, ay, az, bx, by, bz, r) {
  const px = x - ax, py = y - ay, pz = z - az, ex = bx - ax, ey = by - ay, ez = bz - az, h = cl((px * ex + py * ey + pz * ez) / (ex * ex + ey * ey + ez * ez), 0, 1);
  return L3(px - ex * h, py - ey * h, pz - ez * h) - r;
}
function rcone(x, y, z, ax, ay, az, bx, by, bz, r1, r2) { // a capsule whose radius runs from r1 at a to r2 at b
  const bax = bx - ax, bay = by - ay, baz = bz - az, l2 = bax * bax + bay * bay + baz * baz, rr = r1 - r2, a2 = l2 - rr * rr, il2 = 1 / l2;
  const pax = x - ax, pay = y - ay, paz = z - az, yv = pax * bax + pay * bay + paz * baz, zv = yv - l2;
  const qx = pax * l2 - bax * yv, qy = pay * l2 - bay * yv, qz = paz * l2 - baz * yv, x2 = qx * qx + qy * qy + qz * qz, y2 = yv * yv * l2, z2 = zv * zv * l2, k = sign(rr) * rr * rr * x2;
  if (sign(zv) * a2 * z2 > k) return sqrt(x2 + z2) * il2 - r2;
  if (sign(yv) * a2 * y2 < k) return sqrt(x2 + y2) * il2 - r1;
  return (sqrt(x2 * a2 * il2) + yv * rr) * il2 - r1;
}
function star5(px, py, r, rf) {
  const k1x = .809016994375, k1y = -.587785252292, k2x = -k1x, k2y = k1y;
  px = abs(px); let t = 2 * max(k1x * px + k1y * py, 0); px -= t * k1x; py -= t * k1y;
  t = 2 * max(k2x * px + k2y * py, 0); px -= t * k2x; py -= t * k2y; px = abs(px); py -= r;
  const bax = rf * -k1y, bay = rf * k1x - 1, hh = cl((px * bax + py * bay) / (bax * bax + bay * bay), 0, r);
  return L2(px - bax * hh, py - bay * hh) * sign(py * bax - px * bay);
}
let PX = 0, PZ = 0, PK = 0; // polar repetition around an axis: fold (x, z) into one of n sectors, centred on +x
function fold(x, z, n, off = 0) { const s = TAU / n, a = atan2(z, x) - off, k = Math.round(a / s), b = a - k * s, r = L2(x, z); PX = r * cos(b); PZ = r * sin(b); PK = k; }

// A lathe (surface of revolution) from a profile in the (radius, height) half plane. The profile is rounded by corner cutting
// (points flagged 1 stay sharp) and its 2D distance is tabulated once, so a lathe costs one bilinear lookup.
function chaikin(pts, it) {
  let p = pts.map(q => [q[0], q[1], q[2] || 0]); p[0][2] = p[p.length - 1][2] = 1;
  for (let k = 0; k < it; k++) {
    const o = [p[0]];
    for (let i = 0; i < p.length - 1; i++) {
      const a = p[i], b = p[i + 1];
      if (!a[2]) o.push([mix(a[0], b[0], .25), mix(a[1], b[1], .25), 0]);
      if (!b[2]) o.push([mix(a[0], b[0], .75), mix(a[1], b[1], .75), 0]); else o.push(b);
    }
    p = o;
  }
  return p;
}
function poly2(px, py, P) {
  const n = P.length; let d = (px - P[0][0]) ** 2 + (py - P[0][1]) ** 2, s = 1;
  for (let i = 0, j = n - 1; i < n; j = i, i++) {
    const vi = P[i], vj = P[j], ex = vj[0] - vi[0], ey = vj[1] - vi[1], wx = px - vi[0], wy = py - vi[1];
    const h = cl((wx * ex + wy * ey) / (ex * ex + ey * ey || 1), 0, 1), bx = wx - ex * h, by = wy - ey * h; d = min(d, bx * bx + by * by);
    const c1 = py >= vi[1], c2 = py < vj[1], c3 = ex * wy > ey * wx; if ((c1 && c2 && c3) || (!c1 && !c2 && !c3)) s = -s;
  }
  return s * sqrt(d);
}
function lathe(pts, it = 3, res = .016) {
  const P = chaikin(pts, it); let rmax = 0, ymin = 1e9, ymax = -1e9; for (const [r, y] of P) { rmax = max(rmax, r); ymin = min(ymin, y); ymax = max(ymax, y); }
  const pad = .35, y0 = ymin - pad, W = ceil((rmax + pad) / res) + 2, H = ceil((ymax - ymin + 2 * pad) / res) + 2, F = new Float32Array(W * H);
  for (let j = 0; j < H; j++) for (let i = 0; i < W; i++) F[j * W + i] = poly2(i * res, y0 + j * res, P);
  return (x, y, z) => {
    const r = L2(x, z), fx = r / res, fy = (y - y0) / res;
    if (fx >= W - 1 || fy < 0 || fy >= H - 1) return L2(max(r - rmax, 0), max(ymin - y, y - ymax, 0)) + .001; // outside the table: distance to its box, a lower bound
    const i = fx | 0, j = fy | 0, u = fx - i, v = fy - j, o = j * W + i;
    return mix(mix(F[o], F[o + 1], u), mix(F[o + W], F[o + W + 1], u), v);
  };
}

// ── materials (ids match the page's shader table) ──
const MAT = { gold: 0, silver: 1, bronze: 2, brass: 3, copper: 4, ebony: 5, ivory: 6, marbleW: 7, marbleB: 8, walnut: 9, jade: 10, malachite: 11, lapis: 12, ruby: 13, moonstone: 14,
  glass: 15, amber: 16, velvet: 17, porcelain: 18, lacquer: 19, flame: 20, milkglass: 21, sand: 22, filament: 23, roseQuartz: 24, ice: 25 };
const OPAC = { glass: .13, ice: .4, roseQuartz: .82, ruby: .9, amber: .86, flame: .82, milkglass: .9, moonstone: .97 };
let R = 0, G = 0, Bc = 0, OP = 1, EM = 0, MID = 0;
const set = (r, g, b) => { R = r; G = g; Bc = b; };
const mixc = (a, b, t) => set(mix(a[0], b[0], t), mix(a[1], b[1], t), mix(a[2], b[2], t));
function vein(x, y, z, f, w) { const v = abs(sin((x * .9 + y * .6 + z * .5) * f + fbm(x * .7 + 3, y * .7, z * .7) * 7)); return pow(1 - v, w); }
function paint(m, x, y, z, ao) {
  OP = 1; EM = 0; MID = m;
  const n1 = fbm(x * 1.7, y * 1.7, z * 1.7, 3);
  switch (m) {
    case MAT.gold: set(1, .7, .27); { const k = .9 + .1 * n1; R *= k; G *= k; Bc *= k; } break;
    case MAT.silver: set(.93, .93, .91); break;
    case MAT.bronze: { set(.72, .44, .21); const p = cl((.78 - ao) * 2.2, 0, 1) * (.5 + .5 * n1); mixc([R, G, Bc], [.1, .24, .19], p * .85); } break; // verdigris in the hollows
    case MAT.brass: set(.86, .7, .4); break;
    case MAT.copper: set(.93, .54, .4); break;
    case MAT.ebony: { const g = .5 + .5 * sin(y * 26 + fbm(x * 2, y * .5, z * 2, 3) * 9); set(.011 + .012 * g, .009 + .007 * g, .008 + .004 * g); } break;
    case MAT.ivory: { const g = fbm(x * 3, y * .8, z * 3, 3); set(.72 + .06 * g, .64 + .05 * g, .47 + .03 * g); } break;
    case MAT.marbleW: { const v = vein(x, y, z, 1.4, 22) * .85 + vein(x + 9, y, z - 4, 2.6, 40) * .5; set(.83, .82, .79); mixc([R, G, Bc], [.32, .33, .36], min(v, 1)); } break;
    case MAT.marbleB: { const v = vein(x, y, z, 1.2, 28) + vein(x - 5, y + 2, z, 2.4, 50) * .6; set(.011, .011, .013); mixc([R, G, Bc], [.62, .52, .36], min(v, 1)); } break;
    case MAT.walnut: { const t = L2(x + 4.3, z + 1.9) * 3.4 + fbm(x * .6, y * .9, z * .6) * 3.2 + y * .2, f = t - floor(t); const k = sst(.2, .9, f) * .6 + n1 * .4; set(mix(.06, .17, k), mix(.028, .08, k), mix(.014, .036, k)); } break;
    case MAT.jade: { const k = fbm(x * 1.4, y * 1.4, z * 1.4); set(mix(.03, .17, k), mix(.22, .5, k), mix(.1, .27, k)); const c = pow(vn(x * 3 + 5, y * 3, z * 3), 6) * .6; mixc([R, G, Bc], [.6, .75, .62], c); } break;
    case MAT.malachite: { const b = .5 + .5 * sin(L2(x - 2.2, y + 1.1) * 10 + fbm(x * .9, y * .9, z * .9) * 6); const k = pow(b, 3); set(mix(.004, .07, k), mix(.1, .48, k), mix(.04, .24, k)); } break;
    case MAT.lapis: { const k = fbm(x * 2.1, y * 2.1, z * 2.1); set(mix(.012, .05, k), mix(.025, .09, k), mix(.2, .5, k));
      if (h3(floor(x * 14), floor(y * 14), floor(z * 14)) < .045) { set(1, .72, .3); MID = MAT.gold; } // pyrite flecks
      const w = pow(vn(x * 1.2, y * 4, z * 1.2), 8); mixc([R, G, Bc], [.5, .55, .7], w * .5); } break;
    case MAT.ruby: set(.5 + .1 * n1, .005, .022); break;
    case MAT.moonstone: { set(.7, .74, .82); const k = n1; R *= .94 + .06 * k; G *= .95 + .05 * k; } break;
    case MAT.glass: set(.86, .93, 1); break;
    case MAT.amber: set(.7 + .1 * n1, .2 + .08 * n1, .012 + .01 * n1); EM = .06; break;
    case MAT.velvet: set(.3, .006, .02); break;
    case MAT.porcelain: set(.85, .85, .83); break;
    case MAT.lacquer: set(.006, .006, .008); break;
    case MAT.flame: set(1, .4, .05); EM = 1; break;
    case MAT.milkglass: set(.84, .87, .9); EM = .05; break;
    case MAT.sand: { const g = h3(floor(x * 40), floor(y * 40), floor(z * 40)); set(.7 * (.85 + .3 * g), .43 * (.85 + .3 * g), .15); } break;
    case MAT.filament: set(1, .55, .18); EM = 4; break;
    case MAT.roseQuartz: { const k = fbm(x * 1.3, y * 1.3, z * 1.3); set(.78 + .1 * k, .3 + .12 * k, .36 + .1 * k); } break;
    case MAT.ice: set(.62, .82, .96); break;
  }
  for (const k in OPAC) if (MAT[k] === m) OP = OPAC[k];
}

// ── the pedestal every piece stands on: a Staunton foot, bead, stem and collar ──
const PED = lathe([[0, 0, 1], [1.6, 0, 1], [1.74, .09], [1.76, .3], [1.64, .42, 1], [1.64, .48, 1], [1.68, .56], [1.6, .66, 1], [1.35, .74], [1.12, .9], [.95, 1.2], [.8, 1.7],
  [.68, 2.3], [.62, 2.72], [.66, 2.84, 1], [1.02, 2.92], [1.1, 3.02], [1.06, 3.12, 1], [.78, 3.18], [.56, 3.28], [0, 3.32, 1]], 3);
const PED_TOP = 3.26;
const P = (m, d, c) => ({ m: MAT[m], d, c });
function pedestal(base, accent, sy, sr) {
  const k = min(sy, sr);
  return [P(base, (x, y, z) => PED(x / sr, y / sy, z / sr) * k),
    P(accent, (x, y, z) => { x /= sr; y /= sy; z /= sr; return min(torY(x, y - .52, z, 1.668, .052), torY(x, y - 3.02, z, 1.088, .05)) * k; })];
}

// ── the pieces. Each `top(B)` gets B, the height of the collar, and returns its parts. ──
const MODELS = {
  crown: { base: 'ebony', accent: 'gold', top: B => { // KING
    const Rb = y => 1.02 + .16 * cl(y / 1.1, 0, 1);
    return [
      P('gold', (x, y, z) => { y -= B; const r = L2(x, z), Rr = Rb(y);
        let d = box2(r - Rr, y - .58, .085, .55, .04);
        fold(x, z, 8); const sp = rcone(PX, y, PZ, Rr + .02, .95, 0, Rb(1.1) + .12, 1.7, 0, .17, .05);
        d = smin(d, sp, .1); d = min(d, sph(PX - (Rb(1.1) + .13), y - 1.79, PZ, .12));
        d = min(d, max(min(torZ(x, y - 1.08, z, .99, .08), torZ(z, y - 1.08, x, .99, .08)), 1.1 - y)); // the arches
        d = min(d, sph(x, y - 2.22, z, .2), box(x, y - 2.56, z, .05, .2, .05, .024), box(x, y - 2.6, z, .16, .05, .05, .024)); // orb and cross
        d = min(d, torY(x, y - .07, z, Rb(.07) + .05, .065), torY(x, y - 1.06, z, Rb(1.06) + .05, .055));
        return d; }),
      P('velvet', (x, y, z) => { y -= B; return max(ell(x, y - .95, z, .96, .98, .96), .25 - y); }),
      P('ruby', (x, y, z) => { y -= B; fold(x, z, 8, PI / 8); return ell(PX - (Rb(.58) + .07), y - .58, PZ, .09, .15, .13); }),
    ]; } },

  key: { base: 'walnut', accent: 'brass', top: B => [ // KEY
    P('bronze', (x, y, z) => { y -= B;
      let d = cap(x, y, z, 0, .1, 0, 0, 2.3, 0, .14);
      d = smin(d, torY(x, y - 2.22, z, .2, .085), .05); d = smin(d, torY(x, y - 1.98, z, .17, .06), .04);
      const by = y - 3.02; d = min(d, torZ(x, by, z, .68, .12), torZ(x, by, z, .24, .07));
      { const a = atan2(by, x) - PI / 4, s = PI / 2, b = a - Math.round(a / s) * s, r = L2(x, by); d = min(d, cap(r * cos(b), r * sin(b), z, .24, 0, 0, .6, 0, 0, .055)); }
      { const a = atan2(by, x), s = PI / 2, b = a - Math.round(a / s) * s, r = L2(x, by); d = smin(d, sph(r * cos(b) - .84, r * sin(b), z, .11), .05); }
      let bit = box(x - .48, y - .58, z, .34, .36, .07, .025);
      bit = smax(bit, -box(x - .62, y - .62, z, .13, .07, .2), .02); bit = smax(bit, -box(x - .78, y - .36, z, .1, .1, .2), .02);
      return smin(d, bit, .04); }),
  ] },

  sun: { base: 'marbleW', accent: 'gold', top: B => [ // SUN
    P('gold', (x, y, z) => { const yy = y - (B + 1.92);
      let d = ell(x, yy, z, .92, .92, .36);
      const a = atan2(yy, x), s = TAU / 12, k = Math.round(a / s), b = a - k * s, r = L2(x, yy), L = (k & 1) ? 1.9 : 1.45;
      d = smin(d, rcone(r * cos(b), r * sin(b), z * 1.6, .75, 0, 0, L, 0, 0, .24, .035) / 1.35, .12);
      d = smin(d, torZ(x, yy, z - .31, .6, .045), .03); d = smin(d, sph(x, yy, z - .12, .3), .06);
      return d; }),
  ] },

  moon: { base: 'lapis', accent: 'silver', top: B => { // MOON
    const cres = (x, y) => max(L2(x, y) - 1.5, -(L2(x - .7, y + .08) - 1.3));
    return [
      P('moonstone', (x, y, z) => { const yy = y - (B + 1.72), c = cos(-.5), s = sin(-.5), xr = c * x - s * yy, yr = s * x + c * yy, d2 = cres(xr, yr);
        const hz = .07 + .3 * sst(0, -.55, d2), wx = d2 + .07, wy = abs(z) - hz; return min(max(wx, wy), 0) + L2(max(wx, 0), max(wy, 0)) - .07; }),
      P('silver', (x, y, z) => cylY(x + .3, y - (B + .14), z, .12, .22, .04)),
      P('gold', (x, y, z) => { const sx = x - .55, sy = y - (B + 3.0), sz = z - .1; return min(ell(sx, sy, sz, .07, .34, .07), ell(sx, sy, sz, .3, .07, .07)); }),
    ]; } },

  bell: { base: 'ivory', accent: 'bronze', sy: .92, top: B => { // BELL
    const F = lathe([[0, .16, 1], [1.28, .16], [1.52, .04, 1], [1.6, .12], [1.52, .3], [1.24, .66], [1.06, 1.15], [1.0, 1.6], [.94, 1.95], [.72, 2.18], [0, 2.26, 1]], 3);
    return [
      P('bronze', (x, y, z) => { y -= B; return min(F(x, y, z), torY(x, y - .4, z, 1.46, .045), torY(x, y - 1.86, z, .95, .04)); }),
      P('ebony', (x, y, z) => { y -= B; return smin(cylY(x, y - 2.45, z, .19, .25, .05), sph(x, y - 2.95, z, .33), .15); }),
    ]; } },

  flame: { base: 'marbleB', accent: 'brass', top: B => { // FIRE
    const cup = lathe([[0, 0, 1], [.45, 0], [.9, .18], [1.15, .42], [1.2, .52, 1], [1.08, .54, 1], [.85, .4], [0, .34, 1]], 2);
    const S = []; for (let i = 0; i <= 20; i++) { const t = i / 20; S.push([.24 * sin(t * 3.4) * t, .62 + t * 2.9, .1 * sin(t * 2.3 + 1) * t, .9 * pow(1 - t, .85) * (.78 + .22 * sin(PI * min(t * 1.6, 1))) + .03]); }
    const T = []; for (const sx of [-1, 1]) for (let i = 0; i <= 8; i++) { const t = i / 8; T.push([sx * (.42 + .32 * t - .15 * t * t), .75 + t * (sx > 0 ? 1.35 : 1.7), -.1, .42 * pow(1 - t, .9) + .03]); }
    return [
      P('brass', (x, y, z) => cup(x, y - B, z)),
      P('flame', (x, y, z) => { y -= B; let d = 1e9; for (const p of S) d = smin(d, sph(x - p[0], y - p[1], z - p[2], p[3]), .28);
        for (const p of T) d = smin(d, sph(x - p[0], y - p[1], z - p[2], p[3]), .2);
        return d + .05 * (vn(x * 2.5, y * 2.5, z * 2.5) - .5); }, (x, y, z) => { const t = cl((y - B - .2) / 3.3, 0, 1); set(1, mix(.12, .62, pow(t, .7)), mix(.005, .12, t * t)); EM = mix(.55, 1.05, t); }),
    ]; } },

  heart: { base: 'marbleW', accent: 'gold', top: B => [ // LOVE
    P('roseQuartz', (x, y, z) => { const yy = y - B, c = cos(.35), s = sin(.35), xr = c * x + s * z, zr = -s * x + c * z, px = abs(xr);
      const a = .6, ca = cos(a), sa = sin(a), lx = px - .6, ly = yy - 1.6, ex = ca * lx - sa * ly, ey = sa * lx + ca * ly;
      return ell(ex, ey, zr, .8, 1.2, .62); }),
  ] },

  umbrella: { base: 'porcelain', accent: 'silver', sy: .88, top: B => { // RAIN
    const drops = [[.75, 3.65, .45, .15], [-.95, 3.35, -.25, .13], [.15, 4.15, -.65, .12], [-.4, 4.4, .55, .1]];
    return [
      P('lacquer', (x, y, z) => { const yy = y - B, th = atan2(z, x), s2 = sin(4 * th) ** 2, Rr = 2.12 - .08 * s2;
        let d = abs(sph(x, yy - .95, z, Rr)) - (.055 + .045 * pow(1 - s2, 10));
        return smax(d, (1.98 + .2 * s2) - yy, .04); }),
      P('silver', (x, y, z) => { const yy = y - B; let d = cylY(x, yy - 1.55, z, .065, 1.6);
        d = min(d, rcone(x, yy, z, 0, 3.05, 0, 0, 3.52, 0, .1, .03));
        fold(x, z, 8); return min(d, sph(PX - 1.86, yy - 1.97, PZ, .07)); }),
      P('glass', (x, y, z) => { const yy = y - B; let d = 1e9; for (const [dx, dy, dz, r] of drops) d = min(d, smin(sph(x - dx, yy - dy, z - dz, r), rcone(x - dx, yy - dy, z - dz, 0, 0, 0, 0, r * 2.4, 0, r * .55, .01), r * .6)); return d; }),
    ]; } },

  hourglass: { base: 'walnut', accent: 'brass', sy: .85, top: B => [ // TIME
    P('walnut', (x, y, z) => { const yy = y - B; return min(cylY(x, yy - .12, z, 1.2, .12, .05), cylY(x, yy - 3.42, z, 1.2, .12, .05), sph(x, yy - 3.6, z, .16)); }),
    P('brass', (x, y, z) => { const yy = y - B; fold(x, z, 3, PI / 6); return min(cylY(PX - 1.0, yy - 1.77, PZ, .07, 1.6), sph(PX - 1.0, yy - 1.77, PZ, .12), torY(x, yy - .26, z, 1.12, .04), torY(x, yy - 3.28, z, 1.12, .04)); }),
    P('glass', (x, y, z) => { const yy = y - B; return abs(smin(sph(x, yy - .98, z, .8), sph(x, yy - 2.56, z, .8), .3)) - .045; }),
    P('sand', (x, y, z) => { const yy = y - B, r = L2(x, z);
      return min(max(sph(x, yy - .98, z, .73), yy - (.6 + .42 * max(0, 1 - r / .62))), max(sph(x, yy - 2.56, z, .73), yy - 2.28), cylY(x, yy - 1.45, z, .05, .6)); }),
  ] },

  anchor: { base: 'lapis', accent: 'silver', top: B => [ // SHIP
    P('silver', (x, y, z) => { const yy = y - B;
      let d = rcone(x, yy, z, 0, .4, 0, 0, 3.25, 0, .19, .13);
      d = min(d, torZ(x, yy - 3.55, z, .3, .085), cap(x, yy, z, -.95, 3.0, 0, .95, 3.0, 0, .1), sph(abs(x) - .98, yy - 3.0, z, .15));
      d = smin(d, smax(torZ(x, yy - 1.5, z, 1.2, .14), yy - 1.12, .04), .1);
      d = smin(d, rcone(abs(x), yy, z * 1.7, 1.13, 1.08, 0, 1.42, 1.62, 0, .3, .04) / 1.4, .06);
      return smin(d, sph(x, yy - .3, z, .2), .1); }),
  ] },

  bone: { base: 'walnut', accent: 'brass', top: B => [ // DOG
    P('ivory', (x, y, z) => { const yy = y - (B + .66), cy = cos(.5), sy = sin(.5), xr = cy * x + sy * z, zr = -sy * x + cy * z, cz = cos(.18), sz = sin(.18), x2 = cz * xr + sz * yy, y2 = -sz * xr + cz * yy;
      return smin(cap(x2, y2, zr, -1.05, 0, 0, 1.05, 0, 0, .3), sph(abs(x2) - 1.2, abs(y2) - .3, zr, .4), .25); }),
  ] },

  bulb: { base: 'ebony', accent: 'brass', top: B => [ // IDEA
    P('brass', (x, y, z) => { const yy = y - B; return cylY(x, yy - .55, z, .5 + .04 * sin(yy * 34), .5, .04); }),
    P('glass', (x, y, z) => { const yy = y - B, s = smin(cylY(x, yy - 1.25, z, .46, .3), sph(x, yy - 2.35, z, 1.08), .45); return max(abs(s) - .04, 1.02 - yy); }),
    P('brass', (x, y, z) => { const yy = y - B; return min(cap(abs(x), yy, z, .18, 1.0, 0, .32, 2.1, 0, .045), cylY(x, yy - 1.12, z, .2, .12, .04)); }),
    P('filament', (x, y, z) => { const yy = y - B; return cap(abs(x), yy, z, .32, 2.1, 0, 0, 2.45, 0, .065); }),
  ] },

  snail: { base: 'walnut', accent: 'copper', top: B => { // SLOW
    const S = []; for (let i = 0; i <= 36; i++) { const th = i / 36 * 3.6 * PI, g = exp(-.2 * th); S.push([-.15 + 1.0 * g * cos(th - PI / 2), 1.62 + 1.0 * g * sin(th - PI / 2), 0, .62 * g + .03]); }
    return [
      P('copper', (x, y, z) => { const yy = y - B; let d = 1e9; for (const p of S) d = smin(d, sph(x - p[0], yy - p[1], z - p[2], p[3]), .12); return d; },
        (x, y, z) => { const a = atan2(y - B - 1.62, x + .15), r = L2(x + .15, y - B - 1.62), t = mod(a + r * 9, TAU) / TAU; const k = .5 + .5 * sin(t * TAU * 3); set(mix(.5, .95, k), mix(.22, .55, k), mix(.14, .4, k)); }),
      P('jade', (x, y, z) => { const yy = y - B;
        let d = smin(ell(x + .1, yy - .3, z, 1.45, .3, .42), rcone(x, yy, z, 1.0, .4, 0, 1.45, 1.15, 0, .33, .25), .2);
        d = min(d, cap(x, yy, abs(z), 1.42, 1.25, .1, 1.7, 1.95, .24, .055), sph(x - 1.72, yy - 2.0, abs(z) - .25, .1));
        return d; }),
    ]; } },

  horseshoe: { base: 'malachite', accent: 'gold', top: B => [ // LUCK
    P('silver', (x, y, z) => { const yy = y - (B + 1.43), r = L2(x, yy);
      let d = smax(box2(r - 1.12, z, .27, .17, .07), yy - .62, .05);
      d = smax(d, -(L2(r - 1.12, z - .17) - .055), .02);
      for (const b of [.6, 1.05, 1.5]) { const hx = 1.12 * sin(b), hy = -1.12 * cos(b); d = smax(d, -min(cylZ(x - hx, yy - hy, z, .065, .5), cylZ(x + hx, yy - hy, z, .065, .5)), .02); }
      return d; }),
  ] },

  skep: { base: 'walnut', accent: 'gold', sy: .9, top: B => [ // HONEY
    P('amber', (x, y, z) => { const yy = y - B;
      let d = ell(x, yy, z, 1.42, 2.5, 1.42) - .05 * (.5 + .5 * cos(yy * TAU / .32));
      d = smax(d, -yy, .05); d = smax(d, -box(x, yy - .22, z - 1.35, .26, .22, .4, .12), .05);
      return smin(d, sph(x, yy - 2.5, z, .2), .1); }),
    P('amber', (x, y, z) => { const yy = y - B; return smin(sph(x - .02, yy - .2, z - 1.42, .09), rcone(x - .02, yy, z - 1.42, 0, -.05, 0, 0, .14, 0, .14, .06), .05); }), // a drip of honey
    P('ebony', (x, y, z) => { const bx = x - 1.0, by = y - B - 1.95, bz = z - .95; return min(ell(bx, by, bz, .27, .17, .17), sph(bx - .27, by + .02, bz + .05, .12)); },
      (x, y, z) => { const t = (x - 1.0) * 7; if (sin(t * PI) > .1 && x < 1.22) set(.9, .62, .12); }),
    P('glass', (x, y, z) => { const bx = x - .97, by = y - B - 2.2, bz = z - .95; return min(ell(bx + .1, by, bz + .14, .22, .04, .13), ell(bx + .1, by, bz - .14, .22, .04, .13)); }),
  ] },

  acorn: { base: 'jade', accent: 'gold', top: B => [ // OAK
    P('walnut', (x, y, z) => { const yy = y - B; return smin(ell(x, yy - 1.3, z, .8, 1.02, .8), rcone(x, yy, z, 0, .12, 0, 0, .55, 0, .05, .3), .25); }),
    P('bronze', (x, y, z) => { const yy = y - B, th = atan2(z, x);
      let d = max(sph(x, yy - 1.72, z, .9), 1.5 - yy) - .04 * cos(th * 16 + yy * 14) * cos(yy * 30);
      return min(d, cap(x, yy, z, 0, 2.5, 0, .12, 3.05, .05, .085)); }),
  ] },

  nose: { base: 'marbleB', accent: 'gold', top: B => [ // SMELL: a nose broken off a statue, far too big for its plinth
    P('marbleW', (x, y, z) => { const yy = y - B, fx = abs(x);
      let f = ell(x, yy - 1.5, z + .25, 1.0, 1.42, .62); f = smax(f, -(z + .5), .08);                 // the curve of a face, broken off flat behind
      f += .09 * (vn(x * 2.6 + 5, yy * 2.6, z * 2.6) - .5) * sst(.4, .9, L2(x / 1.0, (yy - 1.5) / 1.42)); // chipped round its edge
      f = smin(f, ell(fx - .46, yy - 2.48, z - .2, .46, .16, .24), .2);                                 // brows
      f = smin(f, ell(x, yy - .58, z - .22, .5, .17, .26), .15);                                        // a hint of upper lip
      let n = rcone(x, yy, z, 0, 2.6, .25, 0, 1.3, 1.08, .26, .34);
      n = smin(n, sph(x, yy - 1.15, z - 1.05, .4), .25);
      n = smin(n, ell(fx - .43, yy - .97, z - .7, .32, .27, .34), .2);
      n = smax(n, -ell(fx - .2, yy - .78, z - .9, .11, .08, .16), .05);
      return smin(f, n, .2); }),
  ] },

  rook: { base: 'marbleW', accent: 'gold', top: B => { // TOWER
    const F = lathe([[0, -.2, 1], [.98, -.2], [.9, .3], [.8, 1.5], [.84, 1.72], [1.06, 1.9], [1.1, 2.02, 1], [1.1, 2.8, 1], [0, 2.8, 1]], 3);
    return [
      P('marbleW', (x, y, z) => { const yy = y - B; let d = F(x, yy, z);
        fold(x, z, 6); d = smax(d, -box(PX - 1.0, yy - 2.68, PZ, .35, .25, .16), .03);
        return smax(d, -cylY(x, yy - 2.85, z, .74, .3), .03); }),
      P('gold', (x, y, z) => torY(x, y - B - 1.62, z, .82, .05)),
    ]; } },

  planet: { base: 'ebony', accent: 'gold', top: B => [ // SPACE
    P('lapis', (x, y, z) => sph(x, y - (B + 1.85), z, 1.08)),
    P('gold', (x, y, z) => { const yy = y - (B + 1.85), ca = cos(.42), sa = sin(.42), y1 = ca * yy - sa * z, z1 = sa * yy + ca * z, cb = cos(.28), sb = sin(.28), x2 = cb * x - sb * y1, y2 = sb * x + cb * y1, rr = L2(x2, z1);
      return smax(box2(rr - 1.72, y2, .4, .07, .03), -box2(rr - 1.55, y2, .03, .3), .01); }),
    P('gold', (x, y, z) => cylY(x, y - (B + .4), z, .13, .45, .03)),
    P('moonstone', (x, y, z) => sph(x - 1.75, y - (B + 3.15), z + .3, .2)),
  ] },

  notes: { base: 'ivory', accent: 'gold', top: B => [ // MUSIC
    P('lacquer', (x, y, z) => { const yy = y - B, c = cos(-.4), s = sin(-.4);
      const head = (cx, cy) => { const lx = x - cx, ly = yy - cy; return ell(c * lx - s * ly, s * lx + c * ly, z, .52, .37, .3); };
      return min(head(-.55, .38), head(.72, .88), cap(x, yy, z, -.1, .45, 0, -.1, 2.95, 0, .075), cap(x, yy, z, 1.17, .95, 0, 1.17, 3.35, 0, .075)); }),
    P('gold', (x, y, z) => { const yy = y - B, ang = atan2(.4, 1.27), c = cos(ang), s = sin(ang), lx = x - .535, ly = yy - 3.1; return box(c * lx + s * ly, -s * lx + c * ly, z, .72, .13, .12, .04); }),
  ] },

  crystal: { base: 'marbleW', accent: 'silver', top: B => { // COLD
    const X = [[0, 0, 0, 0, .42, 3.4], [.35, .2, .6, .45, .3, 2.4], [-.3, .25, 2.4, .5, .28, 2.0], [-.1, -.35, 4.0, .42, .3, 2.6], [.3, -.25, 5.3, .65, .22, 1.6]].map(([ox, oz, az, tl, Rr, L]) => {
      const a = [sin(tl) * cos(az), cos(tl), sin(tl) * sin(az)], t = abs(a[1]) < .9 ? [0, 1, 0] : [1, 0, 0];
      let u = [a[1] * t[2] - a[2] * t[1], a[2] * t[0] - a[0] * t[2], a[0] * t[1] - a[1] * t[0]]; const ul = L3(...u); u = u.map(v => v / ul);
      const v = [a[1] * u[2] - a[2] * u[1], a[2] * u[0] - a[0] * u[2], a[0] * u[1] - a[1] * u[0]];
      return { ox, oz, a, u, v, Rr, L, rot: az * 1.7 };
    });
    const sa = sin(.95), ca = cos(.95);
    return [P('ice', (x, y, z) => { const yy = y - B + .25; let d = 1e9;
      for (const c of X) { const px = x - c.ox, pz = z - c.oz, w = px * c.a[0] + yy * c.a[1] + pz * c.a[2], u = px * c.u[0] + yy * c.u[1] + pz * c.u[2], v = px * c.v[0] + yy * c.v[1] + pz * c.v[2];
        const s = PI / 3, a = atan2(v, u) + c.rot, b = a - Math.round(a / s) * s, f = L2(u, v) * cos(b);
        d = min(d, max(f - c.Rr, f * sa + (w - c.L) * ca, -w)); }
      return d; })]; } },

  padlock: { base: 'marbleB', accent: 'gold', top: B => [ // SAFE
    P('brass', (x, y, z) => { const yy = y - B; let d = box(x, yy - 1.0, z, 1.0, .92, .4, .3);
      return smax(d, -min(sph(x, yy - 1.12, z - .42, .15), box(x, yy - .88, z - .42, .065, .22, .15, .02)), .02); }),
    P('silver', (x, y, z) => { const yy = y - B; return min(smax(torZ(x, yy - 1.95, z, .66, .13), 1.95 - yy, .02), cylY(abs(x) - .66, yy - 1.85, z, .13, .14)); }),
  ] },

  ghost: { base: 'ebony', accent: 'silver', top: B => { // BOO
    const eyes = (x, y, z) => { const yy = y - B - .12, xs = x - .12 * sin(yy * 1.6); return min(ell(abs(xs) - .3, yy - 2.42, z - .86, .12, .19, .2), ell(xs, yy - 1.95, z - .9, .16, .22, .22)); };
    return [P('milkglass', (x, y, z) => { const yy = y - B - .12, xs = x - .12 * sin(yy * 1.6);
      let d = smin(sph(xs, yy - 2.25, z, .92), rcone(xs, yy, z, 0, 2.0, 0, 0, .45, 0, .92, 1.12), .3);
      d = smax(d, (.42 + .16 * sin(atan2(z, xs) * 5)) - yy, .06);
      d = smin(d, cap(abs(xs), yy, z, .75, 1.6, .1, 1.25, 2.05, .25, .2), .15);
      return smax(d, -eyes(x, y, z), .04); }, (x, y, z) => { if (eyes(x, y, z) < .05) { set(.012, .012, .016); OP = 1; EM = 0; } })]; } },

  star: { base: 'ebony', accent: 'silver', top: B => [ // STAR
    P('silver', (x, y, z) => { const yy = y - (B + 1.6), d2 = star5(x, -yy, 1.62, .46), k = .5; return max(d2, (abs(z) + k * d2) / sqrt(1 + k * k)); }),
  ] },

  apple: { base: 'ivory', accent: 'gold', top: B => { const cy = B + 1.12; return [ // APPLE
    P('ruby', (x, y, z) => { const yy = y - cy, th = atan2(z, x);
      let d = L3(x, yy * 1.06, z) - 1.15 - .035 * cos(th * 5) * sst(-.5, .8, yy);
      d = smax(d, -sph(x, yy - 1.2, z, .42), .32); return smax(d, -sph(x, yy + 1.22, z, .25), .2); }),
    P('bronze', (x, y, z) => cap(x, y - cy, z, 0, .75, 0, .14, 1.45, .03, .065)),
    P('jade', (x, y, z) => { const lx = x - .5, ly = y - cy - 1.28, lz = z - .05, c = cos(-.5), s = sin(-.5); return ell(c * lx - s * ly, s * lx + c * ly, lz, .55, .07, .26); }),
  ]; } },
};

// ── carving: find the surface on a voxel grid, pull each surface voxel onto it, make it a splat ──
const FLOATS = 20; // per splat: centre xyz, opacity | covariance xx xy xz yy | yz zz, random, material | albedo rgb, occlusion | normal xyz, emission
function carve(name, h = .09) {
  const M = MODELS[name], sy = M.sy || 1, sr = M.sr || 1, parts = [...pedestal(M.base, M.accent, sy, sr), ...M.top(PED_TOP * sy)], np = parts.length;
  let last = 0;
  const D = (x, y, z) => { let d = 1e9, pi = 0; for (let i = 0; i < np; i++) { const v = parts[i].d(x, y, z); if (v < d) { d = v; pi = i; } } last = pi; return d; };
  const x0 = -2.7, y0 = -.25, z0 = -2.7, C = 4, pts = []; let gx = 0, gy = 0, gz = 0, e = h * .25;
  const grad = (x, y, z) => {
    const a = D(x + e, y - e, z - e), b = D(x - e, y - e, z + e), c = D(x - e, y + e, z - e), d = D(x + e, y + e, z + e);
    gx = (a - b - c + d) / (4 * e); gy = (-a - b + c + d) / (4 * e); gz = (-a + b - c + d) / (4 * e);
  };
  // two passes: the pedestal at a coarser pitch, the carving on top finer, each keeping only the surface that belongs to it
  const pass = (h, keep) => {
    const hc = h * C, nx = ceil(5.4 / hc), ny = ceil(8.2 / hc), nz = ceil(5.4 / hc), thr = hc * .87 * 1.6 + h; e = h * .25;
    for (let k = 0; k < nz; k++) for (let j = 0; j < ny; j++) for (let i = 0; i < nx; i++) {
      if (abs(D(x0 + (i + .5) * hc, y0 + (j + .5) * hc, z0 + (k + .5) * hc)) > thr) continue;
      for (let c = 0; c < C; c++) for (let b = 0; b < C; b++) for (let a = 0; a < C; a++) {
        let px = x0 + (i * C + a + .5) * h, py = y0 + (j * C + b + .5) * h, pz = z0 + (k * C + c + .5) * h, d = D(px, py, pz);
        if (abs(d) >= h * .5 || !keep(last)) continue;
        for (let it = 0; it < 3; it++) { grad(px, py, pz); const g2 = gx * gx + gy * gy + gz * gz || 1; px -= d * gx / g2; py -= d * gy / g2; pz -= d * gz / g2; d = D(px, py, pz); }
        if (abs(d) > h * .2 || py < -.02 || !keep(last)) continue;
        const part = last; grad(px, py, pz); const gl = sqrt(gx * gx + gy * gy + gz * gz) || 1;
        pts.push(px, py, pz, gx / gl, gy / gl, gz / gl, part, h);
      }
    }
  };
  pass(h * 1.15, p => p < 2); pass(h * .8, p => p >= 2);
  const n = pts.length / 8, out = new Float32Array(n * FLOATS);
  let top = 0, rad = 0;
  for (let s = 0; s < n; s++) {
    const q = s * 8, px = pts[q], py = pts[q + 1], pz = pts[q + 2], nx_ = pts[q + 3], ny_ = pts[q + 4], nz_ = pts[q + 5], part = parts[pts[q + 6]], hs = pts[q + 7];
    const st = .74 * hs * .01, sn = .13 * hs * .01, s2 = st * st, dn = sn * sn - s2;
    let occ = 0, w = 1; for (let i = 1; i <= 5; i++) { const t = .09 * i; occ += w * (t - D(px + nx_ * t, py + ny_ * t, pz + nz_ * t)); w *= .6; }
    const ao = cl(1 - 1.4 * occ, .08, 1);
    paint(part.m, px, py, pz, ao); if (part.c) part.c(px, py, pz);
    const o = s * FLOATS;
    out[o] = px * .01; out[o + 1] = py * .01; out[o + 2] = pz * .01; out[o + 3] = OP;
    out[o + 4] = s2 + dn * nx_ * nx_; out[o + 5] = dn * nx_ * ny_; out[o + 6] = dn * nx_ * nz_; out[o + 7] = s2 + dn * ny_ * ny_;
    out[o + 8] = dn * ny_ * nz_; out[o + 9] = s2 + dn * nz_ * nz_; out[o + 10] = h3(s, 77, 3); out[o + 11] = MID;
    out[o + 12] = R; out[o + 13] = G; out[o + 14] = Bc; out[o + 15] = ao;
    out[o + 16] = nx_; out[o + 17] = ny_; out[o + 18] = nz_; out[o + 19] = EM;
    top = max(top, py); rad = max(rad, L2(px, pz));
  }
  // shuffle-free: order does not matter, the page sorts every frame it needs to
  return { count: n, data: out, height: top * .01, radius: rad * .01 };
}

if (typeof module !== 'undefined') module.exports = { carve, MODELS };
else self.onmessage = ({ data }) => {
  const t0 = performance.now(), r = carve(data.name, data.h);
  self.postMessage({ id: data.id, name: data.name, count: r.count, data: r.data, height: r.height, radius: r.radius, ms: performance.now() - t0 }, [r.data.buffer]);
};
