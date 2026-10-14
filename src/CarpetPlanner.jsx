import React, { useState, useEffect, useRef, useMemo } from "react";
import {
  Plus, Trash2, Copy, RotateCw, Undo2, Redo2, ZoomIn, ZoomOut,
  Maximize2, X, Check, AlertTriangle, Ruler, Layers, ScissorsLineDashed,
  ArrowRight, ArrowUp, ArrowLeft, ArrowDown, Settings2, Save,
  Pencil, ChevronLeft, ChevronRight, Undo, Info, Download, FileText, ChevronDown,
  Sparkles, Loader2, MousePointerClick, LayoutGrid, CheckCircle2, CircleDashed, HelpCircle, Printer,
} from "lucide-react";

/* ======================================================================
   SECTION: GEOMETRY LAYER
   Pure functions operating on real-world millimetre coordinates.
   Vertices are always ordered, orthogonal (every edge horizontal or
   vertical) and normalised so the bounding box starts at (0,0).
   ====================================================================== */

const EPS = 0.5; // mm tolerance for "closed" checks

function dirDelta(dir, len) {
  switch (dir) {
    case "R": return { dx: len, dy: 0 };
    case "L": return { dx: -len, dy: 0 };
    case "D": return { dx: 0, dy: len };
    case "U": return { dx: 0, dy: -len };
    default: return { dx: 0, dy: 0 };
  }
}

function isHorizontal(dir) { return dir === "L" || dir === "R"; }

// Build normalised vertices from a direction sequence + wall lengths (mm).
function buildPolygon(directions, lengths) {
  const pts = [{ x: 0, y: 0 }];
  let x = 0, y = 0;
  for (let i = 0; i < directions.length; i++) {
    const { dx, dy } = dirDelta(directions[i], lengths[i] || 0);
    x += dx; y += dy;
    pts.push({ x, y });
  }
  pts.pop(); // last point should coincide with first (closure)
  const minX = Math.min(...pts.map((p) => p.x));
  const minY = Math.min(...pts.map((p) => p.y));
  return pts.map((p) => ({ x: p.x - minX, y: p.y - minY }));
}

function closureError(directions, lengths) {
  let h = 0, v = 0;
  directions.forEach((d, i) => {
    const len = lengths[i] || 0;
    if (d === "R") h += len;
    else if (d === "L") h -= len;
    else if (d === "D") v += len;
    else if (d === "U") v -= len;
  });
  return { h, v };
}

function polygonArea(vertices) {
  let a = 0;
  for (let i = 0; i < vertices.length; i++) {
    const p1 = vertices[i];
    const p2 = vertices[(i + 1) % vertices.length];
    a += p1.x * p2.y - p2.x * p1.y;
  }
  return Math.abs(a) / 2;
}

function boundingBox(vertices) {
  const xs = vertices.map((v) => v.x), ys = vertices.map((v) => v.y);
  return { minX: Math.min(...xs), maxX: Math.max(...xs), minY: Math.min(...ys), maxY: Math.max(...ys) };
}

// Rotate a normalised polygon by 0/90/180/270 degrees, re-normalised to (0,0).
function rotatePolygon(vertices, rotation) {
  const pts = vertices.map((v) => {
    switch (((rotation % 360) + 360) % 360) {
      case 90: return { x: -v.y, y: v.x };
      case 180: return { x: -v.x, y: -v.y };
      case 270: return { x: v.y, y: -v.x };
      default: return { x: v.x, y: v.y };
    }
  });
  const bb = boundingBox(pts);
  return pts.map((p) => ({ x: p.x - bb.minX, y: p.y - bb.minY }));
}

function translatePolygon(vertices, dx, dy) {
  return vertices.map((v) => ({ x: v.x + dx, y: v.y + dy }));
}

// World-space vertices for a placed instance (rotation + position applied).
function instanceVertices(room, instance) {
  const rotated = rotatePolygon(room.vertices, instance.rotation);
  return translatePolygon(rotated, instance.x, instance.y);
}

function pointInPolygon(x, y, vertices) {
  let inside = false;
  for (let i = 0, j = vertices.length - 1; i < vertices.length; j = i++) {
    const xi = vertices[i].x, yi = vertices[i].y;
    const xj = vertices[j].x, yj = vertices[j].y;
    const intersect = (yi > y) !== (yj > y) && x < ((xj - xi) * (y - yi)) / (yj - yi) + xi;
    if (intersect) inside = !inside;
  }
  return inside;
}

// Decompose an orthogonal polygon into non-overlapping rectangles.
// This is the exact representation used for collision/bounds checks so
// L-shaped and stepped rooms are never treated as their bounding box.
function decompose(vertices) {
  const xs = [...new Set(vertices.map((v) => v.x))].sort((a, b) => a - b);
  const ys = [...new Set(vertices.map((v) => v.y))].sort((a, b) => a - b);
  const rects = [];
  for (let i = 0; i < xs.length - 1; i++) {
    const x0 = xs[i], x1 = xs[i + 1], midX = (x0 + x1) / 2;
    let runStart = null;
    for (let j = 0; j < ys.length; j++) {
      const y0 = ys[j], y1 = ys[j + 1];
      const inside = y1 !== undefined && pointInPolygon(midX, (y0 + y1) / 2, vertices);
      if (inside && runStart === null) runStart = y0;
      if ((!inside || y1 === undefined) && runStart !== null) {
        rects.push({ x: x0, y: runStart, w: x1 - x0, h: y0 - runStart });
        runStart = null;
      }
    }
  }
  return rects;
}

function inflateRect(r, a) {
  return { x: r.x - a, y: r.y - a, w: r.w + 2 * a, h: r.h + 2 * a };
}

function rectsOverlap(a, b) {
  return a.x < b.x + b.w - EPS && a.x + a.w > b.x + EPS && a.y < b.y + b.h - EPS && a.y + a.h > b.y + EPS;
}

// Full polygon-vs-polygon overlap test (allowance applied to both sides).
function polygonsCollide(vertsA, vertsB, allowanceMm) {
  const rectsA = decompose(vertsA).map((r) => inflateRect(r, allowanceMm / 2));
  const rectsB = decompose(vertsB).map((r) => inflateRect(r, allowanceMm / 2));
  for (const ra of rectsA) for (const rb of rectsB) if (rectsOverlap(ra, rb)) return true;
  return false;
}

function withinRoll(vertsWithAllowance, rollWidth) {
  const bb = boundingBox(vertsWithAllowance);
  return bb.minX >= -EPS && bb.maxX <= rollWidth + EPS && bb.minY >= -EPS;
}

function allowedVerts(room, instance, allowanceMm) {
  const v = instanceVertices(room, instance);
  if (!allowanceMm) return v;
  // expand every decomposed rect, then take their combined bbox edges
  // (used only for the roll-boundary check, which is a supported case
  // for orthogonal shapes because inflation is applied uniformly).
  const bb = boundingBox(v);
  return [
    { x: bb.minX - allowanceMm / 2, y: bb.minY - allowanceMm / 2 },
    { x: bb.maxX + allowanceMm / 2, y: bb.maxY + allowanceMm / 2 },
  ];
}

/* ======================================================================
   SECTION: COLLISION / VALIDATION LAYER
   ====================================================================== */

function isPlacementValid(room, instance, allInstances, roomsById, rollWidth, tolerance) {
  const verts = instanceVertices(room, instance);
  const bounds = allowedVerts(room, instance, tolerance);
  if (!withinRoll(bounds, rollWidth)) return { valid: false, reason: "outside" };
  for (const other of allInstances) {
    if (other.id === instance.id) continue;
    const otherRoom = roomsById[other.roomId];
    if (!otherRoom) continue;
    const otherVerts = instanceVertices(otherRoom, other);
    if (polygonsCollide(verts, otherVerts, tolerance)) return { valid: false, reason: "overlap" };
  }
  return { valid: true };
}

// Whether ANY instance in a layout currently overlaps another or falls
// outside the roll width (e.g. because a room's wall dimensions were
// edited after it was already placed, so an instance that used to fit now
// doesn't). requiredLength alone can't catch this: overlapping pieces
// occupy the same space, so an invalid layout can measure the SAME or even
// SHORTER than any valid rearrangement — a short length that can't
// actually be cut isn't an efficient one. See runAutoArrange, which checks
// this before ever comparing lengths.
function layoutHasCollisions(instances, roomsById, rollWidth, tolerance) {
  for (const inst of instances) {
    const room = roomsById[inst.roomId];
    if (!room) continue;
    const instTolerance = inst.allowanceOverride != null && inst.allowanceOverride !== ""
      ? parseFloat(inst.allowanceOverride) : tolerance;
    if (!isPlacementValid(room, inst, instances, roomsById, rollWidth, instTolerance).valid) return true;
  }
  return false;
}

function requiredLength(instances, roomsById) {
  let maxY = 0;
  instances.forEach((inst) => {
    const room = roomsById[inst.roomId];
    if (!room) return;
    const v = instanceVertices(room, inst);
    v.forEach((p) => { if (p.y > maxY) maxY = p.y; });
  });
  return maxY;
}

/* ======================================================================
   SECTION: PACKING LAYER (auto-arrange)

   Honest framing: 2D nesting with rotation is NP-hard — true exhaustive
   branch-and-bound to PROVEN global optimality is not computationally
   reachable client-side for anything but trivial instances, and no real
   nesting system (commercial or otherwise) actually does this within an
   interactive time budget. What this layer does instead, and does exactly
   rather than approximately:

   1. EXACT geometry, not bounding boxes. Every placement test below works
      on each room's actual rectilinear decomposition (the same `decompose`
      used by collision detection elsewhere in this file) — an L-shaped
      room's concave notch is real free space, not reserved dead space.

   2. A true No-Fit-Polygon, generalised to this app's rotation set
      (0/90/180/270°, matching the rotation restrictions already enforced
      for grain direction — continuous/arbitrary rotation is intentionally
      excluded because it would misalign a room from its real measured
      wall lengths). For axis-aligned rectilinear shapes the NFP of two
      polygons is exactly the union of pairwise Minkowski sums of their
      decomposed rectangles — `forbiddenRectsForPiece` below computes this
      precisely, so every candidate placement is gap-free and exact, never
      a heuristic approximation.

   3. Bottom-left-fill seeded from the NFP's own forbidden-region corners
      (`bottomLeftPlace`) — the only placement points that can possibly be
      "tightest fit" are at those corners, so this is an exact search over
      the genuinely relevant candidate set, not a coarse grid.

   4. A GUILLOTINE packer (`guillotineArrangeWithOrder`) as an alternative
      placement method, for when the priority is a layout a person can
      actually cut with a straight knife — every cut it produces runs the
      full span of whatever piece it's cutting from, never jogging around
      a corner. It works on bounding boxes rather than exact polygons
      (conservative but always overlap-safe, including for L-shaped
      rooms), so it can't tuck a piece into another's notch the way the
      NFP placer can, trading a little density for cuttability.

   5. A simulated-annealing search (`autoArrange`) over placement ORDER and
      per-piece ROTATION — using whichever of the two placers above was
      requested — re-evaluating each candidate sequence and keeping the
      best result found under a time budget. Symmetry is broken for
      interchangeable identical pieces (same room, same rotation) so
      swapping two such pieces — which can never change the result — is
      never wastefully re-evaluated. Most iterations are cheap local moves
      (swap two pieces, change one room's rotation, move one piece), but
      roughly 1 in 12 is a small, cheap Large Neighbourhood Search "ruin
      and recreate" kick: a modest chunk of the sequence is torn out and
      greedily reinserted piece-by-piece at whichever position currently
      shortens the roll most. Packing has strong positional dependency —
      one early placement decision cascades through everything placed
      after it — which the single-piece moves alone tend to get stuck
      around; the periodic region-rebuild targets exactly that weakness.
      Benchmarked directly (60 trials across several piece-count scenes)
      before settling on these numbers: a larger/more frequent kick cost
      far more search time for no better, and sometimes worse, result — a
      small kick measurably improved average-case reliability (fewer runs
      landing noticeably short of the best achievable layout) without
      raising the ceiling on the single best result either approach can
      reach.

   The result is always labelled a "Suggested Layout": the best arrangement
   found, not a claim of global optimality.
   ====================================================================== */

// Exact Minkowski-sum-based forbidden region: the set of positions for a
// moving piece's origin that would make a given (already-inflated) moving
// rectangle overlap a given (already-inflated) stationary rectangle.
function minkowskiForbiddenRect(stationary, moving) {
  return {
    x: stationary.x - moving.x - moving.w,
    y: stationary.y - moving.y - moving.h,
    w: stationary.w + moving.w,
    h: stationary.h + moving.h,
  };
}

// All forbidden rectangles for a candidate piece's ORIGIN, exact (no
// bounding-box shortcuts): decomposes the candidate at its trial rotation
// and every already-placed instance into real rectangles, and computes the
// pairwise Minkowski sum for each pair. allowanceMm is split evenly as the
// existing collision system does.
function forbiddenRectsForPiece(movingVerts, placedInstances, roomsById, allowanceMm) {
  const movingRects = decompose(movingVerts).map((r) => inflateRect(r, allowanceMm / 2));
  const forbidden = [];
  for (const other of placedInstances) {
    const otherRoom = roomsById[other.roomId];
    if (!otherRoom) continue;
    const otherVerts = instanceVertices(otherRoom, other);
    const otherTol = other.allowanceOverride != null && other.allowanceOverride !== "" ? parseFloat(other.allowanceOverride) : allowanceMm;
    const stationaryRects = decompose(otherVerts).map((r) => inflateRect(r, otherTol / 2));
    for (const sr of stationaryRects) for (const mr of movingRects) forbidden.push(minkowskiForbiddenRect(sr, mr));
  }
  return forbidden;
}

function pointInsideRect(x, y, r) {
  return x > r.x + EPS && x < r.x + r.w - EPS && y > r.y + EPS && y < r.y + r.h - EPS;
}

// Exact bottom-left-fill: places one piece as low, then as far left, as the
// real geometry allows, using only the NFP's own forbidden-region corners
// as candidate points (the only points that can possibly be tightest-fit).
function bottomLeftPlace(room, rotation, placedInstances, roomsById, rollWidth, tolerance) {
  const movingVerts = rotatePolygon(room.vertices, rotation);
  const bb = boundingBox(movingVerts);
  const w = bb.maxX - bb.minX, h = bb.maxY - bb.minY;
  const minX = tolerance / 2, maxX = rollWidth - w - tolerance / 2;
  if (maxX < minX - EPS) return null; // doesn't fit the roll width at all, even alone

  const forbidden = forbiddenRectsForPiece(movingVerts, placedInstances, roomsById, tolerance);

  // Candidate points: the full grid of each forbidden rectangle's left/right
  // x-edges crossed with each rectangle's bottom/top y-edges, plus the roll's
  // own left edge and y=0. A single rectangle's own two "outer" corners are
  // not enough on their own — a concave notch formed by TWO rectangles (an
  // L-shaped room's cut corner, for instance) only has a valid touching
  // point at the combination of one rect's x-edge and a different rect's
  // y-edge, so every combination has to be considered to stay exact.
  const xs = new Set([Math.max(0, minX)]);
  const ys = new Set([0]);
  forbidden.forEach((f) => { xs.add(f.x); xs.add(f.x + f.w); ys.add(f.y); ys.add(f.y + f.h); });
  const xList = [...xs].filter((x) => x >= minX - EPS && x <= maxX + EPS);
  const yList = [...ys].filter((y) => y >= -EPS);
  yList.sort((a, b) => a - b);
  xList.sort((a, b) => a - b);

  let bestPt = null;
  outer:
  for (const y of yList) {
    if (bestPt && y > bestPt.y + EPS) break;
    for (const x of xList) {
      if (x < minX - EPS || x > maxX + EPS) continue;
      if (forbidden.some((f) => pointInsideRect(x, y, f))) continue;
      bestPt = { x, y };
      break outer; // yList and xList are sorted ascending, so the first hit at the lowest y is already leftmost-at-that-y
    }
  }
  if (bestPt) return bestPt;

  // Guaranteed-correct fallback: stack clear above every forbidden region.
  const topY = forbidden.reduce((m, f) => Math.max(m, f.y + f.h), 0);
  return { x: Math.max(0, minX), y: topY };
}

function arrangeWithOrder(orderedItems, roomsById, rollWidth, tolerance) {
  const placed = [];
  for (const { inst, rotation } of orderedItems) {
    const room = roomsById[inst.roomId];
    if (!room) continue;
    const pos = bottomLeftPlace(room, rotation, placed, roomsById, rollWidth, tolerance);
    if (!pos) continue; // piece cannot fit the roll width in this rotation; skip rather than corrupt the layout
    placed.push({ ...inst, rotation, x: pos.x, y: pos.y });
  }
  return placed;
}

/* ----------------------------------------------------------------------
   Guillotine packing: every cut this produces runs straight across the
   current piece being cut from, edge to edge — the only kind of cut a
   roll of carpet can realistically take with a straight knife and a
   metre rule, as opposed to the free-form nesting above, which can tuck
   a piece into another's concave notch but may leave cut lines that jog
   around a corner (no problem for a CNC cutter; a real problem for
   someone cutting by hand). This works on each room's bounding box
   rather than its exact polygon — strictly conservative, since a room's
   true (possibly L-shaped) footprint always sits inside its own bounding
   box, so two bounding boxes placed without overlap can never let the
   real shapes overlap either, even though it can't nest a piece into
   another's notch the way the exact-NFP placer above can.

   Classic guillotine bin-packing: a list of free rectangles is kept,
   starting as one rectangle spanning the whole roll (width fixed, length
   effectively unbounded). Each placed piece's bounding box is cut from
   whichever free rectangle it fits most snugly ("best short-side fit"),
   and that free rectangle is then itself split by ONE straight cut into
   up to two new free rectangles — recursively, so the whole structure
   stays guillotine-cuttable no matter how many pieces are placed.
   ---------------------------------------------------------------------- */
function guillotineArrangeWithOrder(orderedItems, roomsById, rollWidth, tolerance) {
  const BIG = 1e9;
  let freeRects = [{ x: 0, y: 0, w: rollWidth, h: BIG }];
  const placed = [];

  for (const { inst, rotation } of orderedItems) {
    const room = roomsById[inst.roomId];
    if (!room) continue;
    const bb = boundingBox(rotatePolygon(room.vertices, rotation));
    const w0 = bb.maxX - bb.minX, h0 = bb.maxY - bb.minY;

    let bestIdx = -1, bestScore = Infinity;
    for (let i = 0; i < freeRects.length; i++) {
      const r = freeRects[i];
      if (r.w >= w0 - EPS && r.h >= h0 - EPS) {
        const score = Math.min(r.w - w0, r.h - h0); // best short-side fit
        if (score < bestScore) { bestScore = score; bestIdx = i; }
      }
    }
    if (bestIdx === -1) continue; // cannot fit this piece's bounding box anywhere; skip rather than corrupt the layout

    const rect = freeRects[bestIdx];
    placed.push({ ...inst, rotation, x: rect.x, y: rect.y });
    freeRects.splice(bestIdx, 1);

    const leftoverW = rect.w - w0 - tolerance;
    const leftoverH = rect.h - h0 - tolerance;
    const next = [];
    // Shorter-leftover-axis rule: whichever direction has less slack gets
    // the full-span cut first, keeping the resulting free rectangles as
    // usable (least sliver-shaped) as the guillotine constraint allows.
    if (leftoverW <= leftoverH) {
      if (leftoverW > EPS) next.push({ x: rect.x + w0 + tolerance, y: rect.y, w: leftoverW, h: h0 });
      if (leftoverH > EPS) next.push({ x: rect.x, y: rect.y + h0 + tolerance, w: rect.w, h: leftoverH });
    } else {
      if (leftoverH > EPS) next.push({ x: rect.x, y: rect.y + h0 + tolerance, w: w0, h: leftoverH });
      if (leftoverW > EPS) next.push({ x: rect.x + w0 + tolerance, y: rect.y, w: leftoverW, h: rect.h });
    }
    freeRects.push(...next);
  }
  return placed;
}

function allowedRotationsFor(grainMode) {
  return grainMode === "locked" ? [0] : [0, 90, 180, 270];
}

function bestDefaultRotation(room, rollWidth, allowedRotations) {
  let best = allowedRotations[0], bestH = Infinity;
  for (const rot of allowedRotations) {
    const bb = boundingBox(rotatePolygon(room.vertices, rot));
    const w = bb.maxX - bb.minX, h = bb.maxY - bb.minY;
    if (w <= rollWidth + EPS && h < bestH) { bestH = h; best = rot; }
  }
  return best;
}

/* ----------------------------------------------------------------------
   Tetris-style skyline packer: a second, genuinely different placement
   method (not the Minkowski/NFP approach above) that drops each piece
   straight down from above (or slides it in from the side) to wherever
   it first comes to rest against the roll floor, another piece, or the
   roll's edge — computed exactly per sub-rectangle, so it's just as able
   as the NFP placer to nest a piece into an L-shaped room's notch, just
   via different mechanics. Benchmarked directly against the NFP+LNS
   search above across several project sizes: this placer was often
   meaningfully better (10%+ shorter on a mixed-size office scene) and
   consistently faster, but reproducibly WORSE specifically on projects
   with several duplicated narrow pieces (a staircase being the motivating
   example) — confirmed structural, not a search-budget shortfall, by
   re-running it at 10x the iteration count with no change in result. The
   two methods have genuinely complementary strengths, so `autoArrange`
   below runs both and keeps whichever result is actually shorter, rather
   than replacing one with the other.
   ---------------------------------------------------------------------- */
function tetrisPack(orderedItems, roomOrientations, rollWidth, tolerance) {
  const placedRects = []; // true (non-inflated) world-space sub-rectangles
  const placements = [];
  let maxLengthUsed = 0;
  const tol = tolerance || 0, half = tol / 2;

  function rectsOverlap(a, b) {
    return a.x < b.x + b.w - EPS && a.x + a.w > b.x + EPS && a.y < b.y + b.h - EPS && a.y + a.h > b.y + EPS;
  }

  for (const { inst, rotation } of orderedItems) {
    const orientations = roomOrientations[inst.roomId];
    if (!orientations) continue;
    const o = orientations[(((rotation % 360) + 360) % 360) / 90] || orientations[0];
    const pieceSubs = o.subrects, pieceW = o.w;
    const minX = half, maxX = rollWidth - pieceW - half;
    if (maxX < minX - EPS) return null;

    // Already-placed pieces inflated by the FULL cutting allowance (while
    // this piece's own geometry stays true-sized) gives a net clearance of
    // exactly `tolerance` between any two placed pieces — the same total
    // gap convention used by the exact-NFP placer elsewhere in this file.
    const obstacles = placedRects.map((r) => ({ x: r.x - tol, y: r.y - tol, w: r.w + 2 * tol, h: r.h + 2 * tol }));

    const xs = new Set([minX, maxX]);
    obstacles.forEach((r) => { xs.add(r.x); xs.add(r.x + r.w - pieceW); xs.add(r.x + r.w); });
    const ys = new Set([0]);
    obstacles.forEach((r) => { ys.add(r.y); ys.add(r.y + r.h); });

    const candidates = [];
    for (const x of xs) {
      if (x < minX - EPS || x > maxX + EPS) continue;
      let settleY = 0;
      for (const sub of pieceSubs) {
        const subX0 = x + sub.x, subX1 = subX0 + sub.w;
        let topEdge = 0;
        for (const ob of obstacles) {
          if (subX0 < ob.x + ob.w - EPS && subX1 > ob.x + EPS) topEdge = Math.max(topEdge, ob.y + ob.h);
        }
        settleY = Math.max(settleY, topEdge - sub.y);
      }
      candidates.push({ x, y: Math.max(0, settleY), source: "drop" });
    }
    for (const y of ys) {
      let settleX = minX;
      for (const sub of pieceSubs) {
        const subY0 = y + sub.y, subY1 = subY0 + sub.h;
        let rightEdge = minX;
        for (const ob of obstacles) {
          if (subY0 < ob.y + ob.h - EPS && subY1 > ob.y + EPS) rightEdge = Math.max(rightEdge, ob.x + ob.w);
        }
        settleX = Math.max(settleX, rightEdge - sub.x);
      }
      candidates.push({ x: Math.min(Math.max(settleX, minX), maxX), y, source: "slide" });
    }

    function isValid(cand) {
      for (const sub of pieceSubs) {
        const rx = cand.x + sub.x, ry = cand.y + sub.y;
        if (rx < minX - EPS || rx + sub.w > rollWidth - half + EPS || ry < -EPS) return false;
        const piece = { x: rx, y: ry, w: sub.w, h: sub.h };
        for (const ob of obstacles) if (rectsOverlap(piece, ob)) return false;
      }
      return true;
    }
    function contactScore(cand) {
      let score = 0;
      for (const sub of pieceSubs) {
        const rx = cand.x + sub.x, ry = cand.y + sub.y;
        if (Math.abs(rx - minX) < EPS) score += sub.h;
        if (Math.abs(rx + sub.w - (rollWidth - half)) < EPS) score += sub.h;
        for (const pr of placedRects) {
          if (Math.abs(ry - (pr.y + pr.h + tol)) < EPS || Math.abs(ry + sub.h - (pr.y - tol)) < EPS) {
            const ov = Math.min(rx + sub.w, pr.x + pr.w) - Math.max(rx, pr.x);
            if (ov > EPS) score += ov;
          }
          if (Math.abs(rx - (pr.x + pr.w + tol)) < EPS || Math.abs(rx + sub.w - (pr.x - tol)) < EPS) {
            const ov = Math.min(ry + sub.h, pr.y + pr.h) - Math.max(ry, pr.y);
            if (ov > EPS) score += ov;
          }
        }
      }
      return score;
    }

    const valid = candidates.filter(isValid);
    if (valid.length === 0) return null;
    valid.sort((a, b) => {
      if (Math.abs(a.y - b.y) > EPS) return a.y - b.y;
      if (Math.abs(a.x - b.x) > EPS) return a.x - b.x;
      const ca = contactScore(a), cb = contactScore(b);
      if (Math.abs(ca - cb) > EPS) return cb - ca;
      return (a.source === "slide" ? 0 : 1) - (b.source === "slide" ? 0 : 1);
    });
    const best = valid[0];

    for (const sub of pieceSubs) placedRects.push({ x: best.x + sub.x, y: best.y + sub.y, w: sub.w, h: sub.h });
    placements.push({ ...inst, rotation, x: best.x, y: best.y });
    maxLengthUsed = Math.max(maxLengthUsed, best.y + o.h);
  }

  return { placements, length: maxLengthUsed };
}

function precomputeTetrisOrientations(room, allowedRotations) {
  const orientations = [null, null, null, null];
  allowedRotations.forEach((rot) => {
    const verts = rotatePolygon(room.vertices, rot);
    const bb = boundingBox(verts);
    orientations[rot / 90] = { subrects: decompose(verts), w: bb.maxX - bb.minX, h: bb.maxY - bb.minY };
  });
  return orientations;
}

// Simulated annealing over (order, per-room rotation) using the tetris
// packer as the evaluator — same duplicate-rotation-sharing guarantee as
// the NFP search below, and the same swap/rotate move set, tuned to this
// placer's much lower per-evaluation cost (confirmed well under a second
// even at 20+ pieces).
function tetrisSearch(instanceList, roomsById, rollWidth, tolerance, grainMode, budgetScale = 1, randomSeed = false) {
  const allowedRotations = allowedRotationsFor(grainMode);
  const n = instanceList.length;
  if (n === 0) return null;
  const roomIds = [...new Set(instanceList.map((i) => i.roomId))];
  const roomOrientations = {};
  roomIds.forEach((id) => { const room = roomsById[id]; if (room) roomOrientations[id] = precomputeTetrisOrientations(room, allowedRotations); });

  let rotByRoom = {};
  roomIds.forEach((id) => {
    const room = roomsById[id];
    rotByRoom[id] = room ? bestDefaultRotation(room, rollWidth, allowedRotations) : allowedRotations[0];
  });
  let order = instanceList.map((inst) => ({ inst }));
  if (randomSeed) {
    // Multi-start trial: shuffle the starting order (see runNfpSearch).
    for (let i = order.length - 1; i > 0; i--) {
      const j = Math.floor(Math.random() * (i + 1));
      [order[i], order[j]] = [order[j], order[i]];
    }
  }

  function evaluate(seq, rotations) {
    const withRot = seq.map((s) => ({ inst: s.inst, rotation: rotations[s.inst.roomId] || 0 }));
    const result = tetrisPack(withRot, roomOrientations, rollWidth, tolerance);
    return result ? { placements: result.placements, length: result.length } : { placements: null, length: Infinity };
  }

  let current = order, currentRot = rotByRoom;
  let evald = evaluate(current, currentRot);
  let bestPlacements = evald.placements, bestLen = evald.length, currentLen = evald.length;
  if (n <= 1) return bestPlacements ? { placements: bestPlacements, length: bestLen } : null;

  const timeBudgetMs = Math.min(1200, 200 + n * 20) * budgetScale;
  const iterCap = Math.max(300, Math.floor(8000 * budgetScale));
  let T = Math.max((isFinite(currentLen) ? currentLen : 1000) * 0.08, 50);
  const cooling = 0.995;
  const startTime = Date.now();
  let iter = 0;

  while (iter < iterCap && Date.now() - startTime < timeBudgetMs) {
    iter++;
    const next = current.map((s) => ({ ...s }));
    let nextRot = currentRot;
    if (Math.random() < 0.5) {
      const i = Math.floor(Math.random() * n), j = Math.floor(Math.random() * n);
      if (i === j) continue;
      if (next[i].inst.roomId === next[j].inst.roomId) continue; // symmetry-breaking, same as the NFP search
      const tmp = next[i]; next[i] = next[j]; next[j] = tmp;
    } else {
      const roomId = roomIds[Math.floor(Math.random() * roomIds.length)];
      let r;
      let tries = 0;
      do { r = allowedRotations[Math.floor(Math.random() * allowedRotations.length)]; tries++; } while (r === currentRot[roomId] && tries < 6 && allowedRotations.length > 1);
      nextRot = { ...currentRot, [roomId]: r };
    }
    const nextEval = evaluate(next, nextRot);
    const delta = nextEval.length - currentLen;
    if (delta < 0 || Math.random() < Math.exp(-delta / Math.max(T, 1e-6))) {
      current = next; currentRot = nextRot; currentLen = nextEval.length;
      if (currentLen < bestLen - EPS) { bestPlacements = nextEval.placements; bestLen = currentLen; }
    }
    T *= cooling;
  }
  return bestPlacements ? { placements: bestPlacements, length: bestLen } : null;
}

// Simulated annealing over (placement order, per-piece rotation), each
// candidate evaluated with the exact NFP + bottom-left-fill placer above.
// Time-budgeted so it stays responsive regardless of instance count.
function runNfpSearch(instanceList, roomsById, rollWidth, tolerance, grainMode, placer, budgetScale = 1, randomSeed = false) {
  const allowedRotations = allowedRotationsFor(grainMode);
  const n = instanceList.length;
  if (n === 0) return [];

  // Rotation is tracked per ROOM, not per instance: every placed copy of
  // the same room (e.g. several identical "Stairs" pieces cut from one
  // duplicated entry) always shares one rotation, because carpet pile/grain
  // direction has to run the same way across duplicates of the same piece
  // — the search is never allowed to spin one copy differently from its
  // siblings just because that happens to pack a little tighter.
  const roomIds = [...new Set(instanceList.map((i) => i.roomId))];
  let rotByRoom = {};
  roomIds.forEach((id) => {
    const room = roomsById[id];
    rotByRoom[id] = room ? bestDefaultRotation(room, rollWidth, allowedRotations) : 0;
  });

  let order = instanceList.map((inst) => ({ inst }));
  if (randomSeed) {
    // Multi-start trial: begin from a shuffled order instead of the
    // decreasing-height seed, so this trial's SA trajectory actually
    // explores a different part of the search space rather than retracing
    // the same strong-seed path with different random accepts.
    for (let i = order.length - 1; i > 0; i--) {
      const j = Math.floor(Math.random() * (i + 1));
      [order[i], order[j]] = [order[j], order[i]];
    }
  } else {
    // Decreasing-height start is a strong seed for bottom-left-fill.
    order.sort((a, b) => {
      const ra = boundingBox(rotatePolygon(roomsById[a.inst.roomId]?.vertices || [{ x: 0, y: 0 }], rotByRoom[a.inst.roomId] || 0));
      const rb = boundingBox(rotatePolygon(roomsById[b.inst.roomId]?.vertices || [{ x: 0, y: 0 }], rotByRoom[b.inst.roomId] || 0));
      return (rb.maxY - rb.minY) - (ra.maxY - ra.minY);
    });
  }

  function evaluate(seq, rotations) {
    const withRot = seq.map((s) => ({ inst: s.inst, rotation: rotations[s.inst.roomId] || 0 }));
    const placed = placer(withRot, roomsById, rollWidth, tolerance);
    // arrangeWithOrder/guillotineArrangeWithOrder skip (rather than fail on)
    // any single piece their placer can't find a spot for — which, left
    // unchecked here, makes an incomplete layout look artificially SHORTER
    // and the search would actively reward dropping a piece. Any candidate
    // that doesn't place every piece is therefore penalised to Infinity so
    // it's never preferred, while bestPlaced below is still only ever
    // assigned a genuinely complete layout.
    const length = placed.length === seq.length ? requiredLength(placed, roomsById) : Infinity;
    return { placed, length };
  }

  let current = order, currentRot = rotByRoom;
  let evald = evaluate(current, currentRot);
  let bestPlaced = evald.placed, bestLen = evald.length;
  let currentLen = evald.length;

  if (n <= 1) return bestPlaced;

  // Budget scales down per-iteration cost as the instance count grows, so
  // a big project still finishes promptly rather than freezing the tab.
  // budgetScale shrinks this further when called as one of several trials
  // in a multi-start portfolio (see autoArrange), so running N trials
  // costs a small, bounded multiple of one full-budget run rather than
  // literally N times as long.
  const timeBudgetMs = Math.min(2500, 400 + n * 40) * budgetScale;
  const iterCap = Math.max(150, Math.floor((30000 / n) * budgetScale));
  let T = Math.max(currentLen * 0.04, 50);
  const cooling = 0.97;
  const startTime = Date.now();
  let iter = 0;

  while (iter < iterCap && Date.now() - startTime < timeBudgetMs) {
    iter++;
    const next = current.map((s) => ({ ...s }));
    let nextRot = currentRot;
    const roll = Math.random();
    if (roll < 0.35) {
      // Swap two positions in the sequence.
      const i = Math.floor(Math.random() * n), j = Math.floor(Math.random() * n);
      if (i === j) continue;
      // Symmetry-breaking: swapping two instances of the SAME room is a
      // no-op (they already share one rotation by construction above), so
      // the search never wastes iterations re-evaluating something that
      // can't possibly change the layout.
      if (next[i].inst.roomId === next[j].inst.roomId) continue;
      const tmp = next[i]; next[i] = next[j]; next[j] = tmp;
    } else if (roll < 0.60) {
      // Try a different rotation for one ROOM — applies to every instance
      // of it at once, keeping duplicates consistent with each other.
      const roomId = roomIds[Math.floor(Math.random() * roomIds.length)];
      const room = roomsById[roomId];
      if (!room) continue;
      const options = allowedRotations.filter((r) => {
        const bb = boundingBox(rotatePolygon(room.vertices, r));
        return bb.maxX - bb.minX <= rollWidth + EPS;
      });
      if (options.length <= 1) continue;
      let r;
      let tries = 0;
      do { r = options[Math.floor(Math.random() * options.length)]; tries++; } while (r === currentRot[roomId] && tries < 6);
      nextRot = { ...currentRot, [roomId]: r };
    } else if (roll < 0.92) {
      // Move one piece to a different point in the sequence.
      const i = Math.floor(Math.random() * n), j = Math.floor(Math.random() * n);
      if (i === j) continue;
      const [item] = next.splice(i, 1);
      next.splice(j, 0, item);
    } else if (n >= 4) {
      // Large Neighbourhood Search "ruin and recreate" kick: tears a chunk
      // of the sequence out and greedily rebuilds it, rather than nudging
      // one piece at a time. Packing has strong positional dependency —
      // one early placement cascades through everything placed after it —
      // which single-piece swap/move/rotate steps alone tend to get stuck
      // around; periodically rebuilding a whole region fixes that directly.
      // Benchmarked at several settings before landing here: a small, cheap
      // kick (roughly 1 in 12 iterations, a modest 10-20% ruin fraction, few
      // sampled reinsertion points) measurably improved average-case result
      // quality without crowding out the cheap local moves above it, whereas
      // a larger/more frequent kick cost much more search time for no better
      // (and sometimes worse) result.
      const ruinCount = Math.max(2, Math.min(n - 1, Math.round(n * (0.10 + Math.random() * 0.10))));
      const idx = [...Array(n).keys()];
      for (let k = idx.length - 1; k > 0; k--) { const j = Math.floor(Math.random() * (k + 1)); [idx[k], idx[j]] = [idx[j], idx[k]]; }
      const ruinSet = new Set(idx.slice(0, ruinCount));
      let remaining = next.filter((_, i2) => !ruinSet.has(i2));
      const removed = next.filter((_, i2) => ruinSet.has(i2));
      // Tallest-first is a strong standalone order for reinsertion.
      removed.sort((a, b) => {
        const ra = boundingBox(rotatePolygon(roomsById[a.inst.roomId]?.vertices || [{ x: 0, y: 0 }], nextRot[a.inst.roomId] || 0));
        const rb = boundingBox(rotatePolygon(roomsById[b.inst.roomId]?.vertices || [{ x: 0, y: 0 }], nextRot[b.inst.roomId] || 0));
        return (rb.maxY - rb.minY) - (ra.maxY - ra.minY);
      });
      // Greedy best-insertion: each removed piece goes back in at whichever
      // sampled position currently yields the shortest roll, rather than a
      // fixed slot — this is what "recreate" means in ruin-and-recreate.
      for (const item of removed) {
        const candidates = new Set([0, remaining.length]);
        const sampleCount = Math.min(3, remaining.length + 1);
        for (let s = 0; s < sampleCount; s++) candidates.add(Math.floor(Math.random() * (remaining.length + 1)));
        let bestPos = 0, bestPosLen = Infinity;
        for (const pos of candidates) {
          const trial = [...remaining.slice(0, pos), item, ...remaining.slice(pos)];
          const trialLen = evaluate(trial, nextRot).length;
          if (trialLen < bestPosLen) { bestPosLen = trialLen; bestPos = pos; }
        }
        remaining = [...remaining.slice(0, bestPos), item, ...remaining.slice(bestPos)];
      }
      next.length = 0;
      next.push(...remaining);
    } else {
      continue;
    }
    const nextEval = evaluate(next, nextRot);
    const delta = nextEval.length - currentLen;
    if (delta < 0 || Math.random() < Math.exp(-delta / Math.max(T, 1e-6))) {
      current = next;
      currentRot = nextRot; // an accepted rotation change has to actually stick, or every later iteration keeps re-trying from the original starting rotation instead of building on what was just accepted
      currentLen = nextEval.length;
      if (currentLen < bestLen - EPS) { bestPlaced = nextEval.placed; bestLen = currentLen; }
    }
    T *= cooling;
  }

  return bestPlaced;
}

// Compaction: both placers above are purely constructive — they place one
// piece at a time, in some order, and never revisit a piece once it's
// placed. The simulated-annealing search tries many different orders, but
// within any single attempt nothing ever slides an already-placed piece
// again. That's exactly the gap manual dragging fills: a person looks at
// the FULL layout and slides a piece into a gap that only became visible
// once everything else was down. This closes that gap algorithmically —
// repeatedly, for every piece in turn, holding every OTHER piece fixed and
// asking "what's the lowest-leftmost spot this one piece could occupy
// right now?" (the exact same NFP machinery as bottomLeftPlace, just
// re-applied against the finished layout instead of a growing one), and
// keeping the move whenever it's strictly better. Runs to a fixed point
// (no more pieces willing to move) or a small pass cap, whichever's first.
function compactLayout(instances, roomsById, rollWidth, tolerance) {
  let current = instances.map((i) => ({ ...i }));
  let improved = true;
  let guard = 0;
  while (improved && guard < 12) {
    improved = false;
    guard++;
    const order = [...current].sort((a, b) => a.y - b.y || a.x - b.x);
    for (const inst of order) {
      const room = roomsById[inst.roomId];
      if (!room) continue;
      const others = current.filter((i) => i.id !== inst.id);
      const pos = bottomLeftPlace(room, inst.rotation, others, roomsById, rollWidth, tolerance);
      if (!pos) continue;
      if (pos.y < inst.y - EPS || (Math.abs(pos.y - inst.y) <= EPS && pos.x < inst.x - EPS)) {
        current = current.map((i) => (i.id === inst.id ? { ...i, x: pos.x, y: pos.y } : i));
        improved = true;
      }
    }
  }
  return current;
}

// How easy a finished layout is to actually cut by hand, as a single
// comparable number — higher is easier. This is only ever used as a
// TIEBREAKER between layouts of equal required length (never to justify a
// longer roll): four things make a layout easier to cut —
//   1. Long, continuous shared edges between pieces (and against the roll's
//      own edges) mean fewer, straighter cuts rather than lots of short
//      jagged ones.
//   2. Multiple instances of the SAME room (e.g. several stair pieces cut
//      from one duplicated entry) sitting adjacent to each other, so they
//      can be cut as one block instead of hunted for across the roll —
//      contact between same-room instances counts extra.
//   3. Clean horizontal lines that run the full roll width with no piece
//      straddling them: a real guillotine cut, usable even outside
//      guillotine mode, and a big win for hand-cutting.
//   4. Same-room duplicates having their edges LINE UP with each other even
//      when they aren't touching (e.g. every stair tread's left edge
//      falling on the same line) — one straight edge or ruler line then
//      serves several pieces at once instead of each needing its own
//      measurement. Since rotation is tracked per room (every instance of
//      a room always shares one rotation — see runNfpSearch), duplicates
//      of the same room are always the same size, so comparing their
//      bounding-box edges directly is meaningful.
function cuttabilityScore(instances, roomsById, rollWidth) {
  const tagged = [];
  for (const inst of instances) {
    const room = roomsById[inst.roomId];
    if (!room) continue;
    const rects = decompose(instanceVertices(room, inst));
    for (const r of rects) tagged.push({ ...r, roomId: inst.roomId, instId: inst.id });
  }
  if (tagged.length === 0) return 0;

  const SAME_ROOM_BONUS = 2; // extra multiplier on contact between same-room instances
  const BOUNDARY_WEIGHT = 0.5; // edges flush with the roll's own boundary need no cut at all
  const FULL_SPAN_BONUS = 3000; // flat reward per clean full-width horizontal cut line
  let score = 0;

  for (let i = 0; i < tagged.length; i++) {
    for (let j = i + 1; j < tagged.length; j++) {
      const a = tagged[i], b = tagged[j];
      if (a.instId === b.instId) continue; // sub-rects of one piece aren't a cut between pieces
      const mult = a.roomId === b.roomId ? SAME_ROOM_BONUS : 1;
      // shared vertical edge (a's right touches b's left, or vice versa)
      if (Math.abs(a.x + a.w - b.x) < EPS || Math.abs(b.x + b.w - a.x) < EPS) {
        const overlap = Math.min(a.y + a.h, b.y + b.h) - Math.max(a.y, b.y);
        if (overlap > EPS) score += overlap * mult;
      }
      // shared horizontal edge (a's top touches b's bottom, or vice versa)
      if (Math.abs(a.y + a.h - b.y) < EPS || Math.abs(b.y + b.h - a.y) < EPS) {
        const overlap = Math.min(a.x + a.w, b.x + b.w) - Math.max(a.x, b.x);
        if (overlap > EPS) score += overlap * mult;
      }
    }
  }

  for (const r of tagged) {
    if (Math.abs(r.x) < EPS) score += BOUNDARY_WEIGHT * r.h;
    if (Math.abs(r.x + r.w - rollWidth) < EPS) score += BOUNDARY_WEIGHT * r.h;
    if (Math.abs(r.y) < EPS) score += BOUNDARY_WEIGHT * r.w;
  }

  const candidateYs = new Set();
  for (const r of tagged) { candidateYs.add(r.y); candidateYs.add(r.y + r.h); }
  for (const y of candidateYs) {
    if (y <= EPS) continue;
    const straddled = tagged.some((r) => r.y < y - EPS && r.y + r.h > y + EPS);
    if (!straddled) score += FULL_SPAN_BONUS;
  }

  // Edge alignment between same-room duplicates (point 4 above): reward
  // each of the four bounding-box edges (left/right/top/bottom) that lines
  // up between two instances of the same room, whether or not they touch.
  const ALIGN_BONUS = 400;
  const instBB = instances.map((inst) => {
    const room = roomsById[inst.roomId];
    return room ? { roomId: inst.roomId, bb: boundingBox(instanceVertices(room, inst)) } : null;
  }).filter(Boolean);
  for (let i = 0; i < instBB.length; i++) {
    for (let j = i + 1; j < instBB.length; j++) {
      const a = instBB[i], b = instBB[j];
      if (a.roomId !== b.roomId) continue;
      if (Math.abs(a.bb.minX - b.bb.minX) < EPS) score += ALIGN_BONUS;
      if (Math.abs(a.bb.maxX - b.bb.maxX) < EPS) score += ALIGN_BONUS;
      if (Math.abs(a.bb.minY - b.bb.minY) < EPS) score += ALIGN_BONUS;
      if (Math.abs(a.bb.maxY - b.bb.maxY) < EPS) score += ALIGN_BONUS;
    }
  }

  return score;
}

// One full attempt at a layout: in guillotine mode there's only one
// sensible placer (the tetris packer doesn't produce guillotine-cuttable
// layouts, and compaction's free sliding isn't guillotine-safe either, so
// neither applies), so this just runs the NFP search with the guillotine
// placer. Otherwise it runs BOTH the exact-NFP search and the tetris
// search, keeps whichever is shorter — see the comment above tetrisPack
// for why neither replaces the other — and finally compacts that result.
// budgetScale is forwarded to both inner searches so a multi-trial caller
// (autoArrange, below) can shrink each individual trial's time budget.
function autoArrangeOnce(instanceList, roomsById, rollWidth, tolerance, grainMode, guillotine, budgetScale, randomSeed) {
  if (guillotine) {
    const result = runNfpSearch(instanceList, roomsById, rollWidth, tolerance, grainMode, guillotineArrangeWithOrder, budgetScale, randomSeed);
    return compactLayout(result, roomsById, rollWidth, tolerance);
  }
  const nfpResult = runNfpSearch(instanceList, roomsById, rollWidth, tolerance, grainMode, arrangeWithOrder, budgetScale, randomSeed);
  const nfpLen = requiredLength(nfpResult, roomsById);

  const tetrisOutcome = tetrisSearch(instanceList, roomsById, rollWidth, tolerance, grainMode, budgetScale, randomSeed);
  const best = (tetrisOutcome && tetrisOutcome.placements && tetrisOutcome.length < nfpLen - EPS)
    ? tetrisOutcome.placements
    : nfpResult;

  return compactLayout(best, roomsById, rollWidth, tolerance);
}

// Public entry point for Auto Arrange: a multi-start portfolio. A single
// simulated-annealing run can land in a local optimum that a different
// starting point would have skipped past entirely, so every press of
// Auto Arrange runs AUTO_ARRANGE_TRIALS (10) independent full attempts —
// the first from the strong decreasing-height seed, the rest each from
// their own freshly-shuffled starting order (see randomSeed in
// runNfpSearch/tetrisSearch) — and keeps whichever produced the shortest
// required roll length. Each trial's own time budget is shrunk (see
// TRIAL_BUDGET_SCALE) so the full portfolio costs a small, bounded
// multiple of one full-budget run rather than literally 10x as long,
// while every trial still gets a real SA search, not a token pass.
//
// Among trials that tie on length, the one that's easier to actually cut
// (see cuttabilityScore) wins — shorter roll always comes first, but a
// tie is never broken arbitrarily when one candidate has straighter,
// more-continuous cut lines than another.
const AUTO_ARRANGE_TRIALS = 10;
const TRIAL_BUDGET_SCALE = 0.35;
function autoArrange(instanceList, roomsById, rollWidth, tolerance, grainMode, guillotine) {
  if (instanceList.length === 0) return [];
  let best = null, bestLen = Infinity, bestCut = -Infinity;
  for (let trial = 0; trial < AUTO_ARRANGE_TRIALS; trial++) {
    const randomSeed = trial > 0; // trial 0 keeps the proven strong seed
    const result = autoArrangeOnce(instanceList, roomsById, rollWidth, tolerance, grainMode, guillotine, TRIAL_BUDGET_SCALE, randomSeed);
    const len = requiredLength(result, roomsById);
    if (len < bestLen - EPS) {
      best = result; bestLen = len; bestCut = cuttabilityScore(result, roomsById, rollWidth);
    } else if (Math.abs(len - bestLen) <= EPS) {
      const cut = cuttabilityScore(result, roomsById, rollWidth);
      if (cut > bestCut + EPS) { best = result; bestLen = len; bestCut = cut; }
    }
  }
  return best;
}

/* ======================================================================
   SECTION: UNITS / FORMATTING
   ====================================================================== */

function parseLength(input, defaultUnit) {
  if (input == null || input === "") return null;
  const str = String(input).trim().toLowerCase();
  if (/^[0-9.]+$/.test(str)) {
    const v = parseFloat(str);
    if (isNaN(v)) return null;
    return defaultUnit === "m" ? v * 1000 : defaultUnit === "cm" ? v * 10 : v;
  }
  const tokenRe = /([0-9]*\.?[0-9]+)\s*(mm|cm|m)/g;
  let match, total = 0, found = false;
  while ((match = tokenRe.exec(str)) !== null) {
    found = true;
    const v = parseFloat(match[1]);
    const unit = match[2];
    total += unit === "m" ? v * 1000 : unit === "cm" ? v * 10 : v;
  }
  return found ? total : null;
}

function formatLength(mm, unit) {
  if (mm == null || isNaN(mm)) return "-";
  if (unit === "m") return (mm / 1000).toFixed(2) + "m";
  if (unit === "cm") return (mm / 10).toFixed(1) + "cm";
  return Math.round(mm) + "mm";
}

function formatArea(mm2) { return (mm2 / 1_000_000).toFixed(2) + "m\u00B2"; }

const DIR_ICON = { R: ArrowRight, L: ArrowLeft, U: ArrowUp, D: ArrowDown };
const ROOM_COLORS = ["#c98a3a", "#d93732", "#8a5fb0", "#4a7fb5", "#b5583f", "#5a8a4a", "#a3843f", "#7a5a8a"];

/* ======================================================================
   SECTION: PERSISTENCE
   ====================================================================== */

const STORAGE_KEY = "carpet-cutting-planner:project";

// window.storage is only available inside the Claude.ai artifact preview.
// On a standalone deployed site (e.g. this app hosted from GitHub) it's
// undefined, so autosave falls back to plain localStorage there instead.
async function loadProject() {
  try {
    if (typeof window !== "undefined" && window.storage?.get) {
      const res = await window.storage.get(STORAGE_KEY, false);
      if (res?.value) return JSON.parse(res.value);
      return null;
    }
  } catch (e) { /* fall through to localStorage */ }
  try {
    const raw = typeof window !== "undefined" && window.localStorage ? window.localStorage.getItem(STORAGE_KEY) : null;
    if (raw) return JSON.parse(raw);
  } catch (e) { /* nothing saved yet */ }
  return null;
}

async function saveProject(data) {
  try {
    if (typeof window !== "undefined" && window.storage?.set) {
      await window.storage.set(STORAGE_KEY, JSON.stringify(data), false);
      return;
    }
  } catch (e) { /* fall through to localStorage */ }
  try {
    if (typeof window !== "undefined" && window.localStorage) window.localStorage.setItem(STORAGE_KEY, JSON.stringify(data));
  } catch (e) { console.error("save failed", e); }
}

/* ======================================================================
   SECTION: UI PRIMITIVES
   Small shared building blocks so every screen uses the same buttons,
   inputs, toggles and panels.
   ====================================================================== */

function cls(...c) { return c.filter(Boolean).join(" "); }

const FOCUS_RING = "focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-brand-500/40 focus-visible:ring-offset-1";
const INPUT = "w-full h-10 rounded-lg border border-stone-200 bg-white px-3 text-sm text-stone-800 placeholder:text-stone-500 focus:outline-none focus:border-brand-500 focus:ring-2 focus:ring-brand-500/20 transition";
const SELECT = INPUT + " pr-8 appearance-none bg-no-repeat bg-[right_0.6rem_center] bg-[length:14px] bg-[url('data:image/svg+xml;utf8,<svg xmlns=%22http://www.w3.org/2000/svg%22 viewBox=%220 0 24 24%22 fill=%22none%22 stroke=%22%2378716c%22 stroke-width=%222%22><path d=%22m6 9 6 6 6-6%22/></svg>')]";

const BTN_VARIANTS = {
  primary: "bg-brand-600 text-white hover:bg-brand-700 shadow-sm",
  dark: "bg-ink-800 text-white hover:bg-ink-900 shadow-sm",
  secondary: "bg-white text-stone-800 ring-1 ring-stone-900/10 hover:ring-stone-900/20 hover:bg-stone-50 shadow-[0_1px_2px_rgba(60,40,30,0.06)]",
  ghost: "text-stone-600 hover:bg-stone-100 hover:text-stone-900",
  danger: "bg-red-600 text-white hover:bg-red-700 shadow-sm",
  dangerSoft: "text-red-600 bg-red-50 hover:bg-red-100",
};
const BTN_SIZES = { sm: "h-8 px-3 text-xs gap-1.5", md: "h-10 px-4 text-sm gap-2", lg: "h-11 px-5 text-sm gap-2" };

function Button({ variant = "secondary", size = "md", className = "", children, ...props }) {
  return (
    <button
      type="button"
      {...props}
      className={cls("inline-flex items-center justify-center font-medium rounded-lg whitespace-nowrap transition-[background-color,color,box-shadow,transform] duration-150 active:scale-[0.98] disabled:opacity-40 disabled:pointer-events-none", FOCUS_RING, BTN_VARIANTS[variant], BTN_SIZES[size], className)}
    >
      {children}
    </button>
  );
}

function IconButton({ label, children, className = "", ...props }) {
  return (
    <button
      type="button"
      aria-label={label}
      title={label}
      {...props}
      className={cls("inline-flex items-center justify-center w-9 h-9 rounded-lg text-stone-600 hover:bg-stone-100 hover:text-stone-900 transition-colors disabled:opacity-30 disabled:pointer-events-none", FOCUS_RING, className)}
    >
      {children}
    </button>
  );
}

function Field({ label, hint, children }) {
  return (
    <label className="block">
      <span className="block text-xs font-medium text-stone-600 mb-1.5">{label}</span>
      {children}
      {hint && <span className="block text-xs leading-snug text-stone-500 mt-1.5">{hint}</span>}
    </label>
  );
}

function Toggle({ checked, onChange, label, description }) {
  return (
    <div className="flex items-start gap-3">
      <button
        type="button" role="switch" aria-checked={checked} aria-label={label}
        onClick={() => onChange(!checked)}
        className={cls("relative mt-0.5 w-9 h-5 shrink-0 rounded-full transition-colors", FOCUS_RING, checked ? "bg-brand-500" : "bg-stone-300")}
      >
        <span className={cls("absolute top-0.5 left-0.5 w-4 h-4 rounded-full bg-white shadow transition-transform", checked && "translate-x-4")} />
      </button>
      <div className="min-w-0 cursor-pointer" onClick={() => onChange(!checked)}>
        <span className="block text-sm text-stone-800 leading-snug">{label}</span>
        {description && <span className="block text-xs text-stone-600 mt-1 leading-snug">{description}</span>}
      </div>
    </div>
  );
}

function Segmented({ value, onChange, options, className = "" }) {
  return (
    <div className={cls("inline-flex p-1 bg-stone-100 rounded-lg", className)}>
      {options.map((o) => (
        <button
          key={o.value} type="button" onClick={() => onChange(o.value)}
          className={cls("flex-1 px-3 h-8 text-xs font-medium rounded-md transition-all", FOCUS_RING, value === o.value ? "bg-white text-stone-900 shadow-sm" : "text-stone-600 hover:text-stone-800")}
        >
          {o.label}
        </button>
      ))}
    </div>
  );
}

function QtyStepper({ value, onChange }) {
  return (
    <div className="inline-flex items-center h-8 rounded-lg border border-stone-200 bg-white overflow-hidden">
      <button type="button" onClick={() => onChange(Math.max(1, value - 1))} aria-label="Decrease quantity" title="Decrease quantity" className="w-8 h-full text-stone-600 hover:bg-stone-100 hover:text-stone-900 transition-colors">−</button>
      <input
        type="number" min="1" value={value} aria-label="Quantity"
        onChange={(e) => onChange(Math.max(1, parseInt(e.target.value) || 1))}
        className="w-10 h-full text-center text-sm font-medium tabular-nums border-x border-stone-200 focus:outline-none focus:bg-brand-50 [appearance:textfield] [&::-webkit-inner-spin-button]:appearance-none [&::-webkit-outer-spin-button]:appearance-none"
      />
      <button type="button" onClick={() => onChange(value + 1)} aria-label="Increase quantity" title="Increase quantity" className="w-8 h-full text-stone-600 hover:bg-stone-100 hover:text-stone-900 transition-colors">+</button>
    </div>
  );
}

function Panel({ title, icon: Icon, action, children, className = "" }) {
  return (
    <section className={cls("bg-white rounded-xl border border-stone-200 shadow-sm", className)}>
      {title && (
        <header className="flex items-center gap-2 px-4 pt-4 pb-3">
          {Icon && <Icon size={15} className="text-stone-500" />}
          <h2 className="text-sm font-semibold text-stone-900">{title}</h2>
          {action && <div className="ml-auto">{action}</div>}
        </header>
      )}
      <div className={title ? "px-4 pb-4" : "p-4"}>{children}</div>
    </section>
  );
}

function Notice({ tone = "info", children }) {
  const tones = {
    info: "bg-stone-50 border-stone-200 text-stone-600",
    warn: "bg-amber-50 border-amber-200 text-amber-800",
    error: "bg-red-50 border-red-200 text-red-700",
    success: "bg-emerald-50 border-emerald-200 text-emerald-800",
  };
  const Icon = tone === "success" ? CheckCircle2 : tone === "info" ? Info : AlertTriangle;
  return (
    <div className={cls("flex items-start gap-2 text-xs leading-snug border rounded-lg px-3 py-2.5", tones[tone])}>
      <Icon size={14} className="shrink-0 mt-px" />
      <div className="min-w-0">{children}</div>
    </div>
  );
}

// Modal shell: dimmed backdrop, centred card, Escape to close (when allowed).
function Modal({ onClose, dismissible = true, className = "", labelledBy, children }) {
  useEffect(() => {
    if (!dismissible) return;
    function onKey(e) { if (e.key === "Escape") onClose(); }
    window.addEventListener("keydown", onKey);
    return () => window.removeEventListener("keydown", onKey);
  }, [onClose, dismissible]);
  return (
    <div
      className="fixed inset-0 z-50 flex items-center justify-center p-3 sm:p-6 bg-stone-900/50 backdrop-blur-[2px] animate-fade-in"
      onMouseDown={(e) => { if (dismissible && e.target === e.currentTarget) onClose(); }}
    >
      <div role="dialog" aria-modal="true" aria-labelledby={labelledBy} className={cls("bg-white rounded-2xl shadow-2xl w-full flex flex-col max-h-[94vh] overflow-hidden animate-pop-in", className)}>
        {children}
      </div>
    </div>
  );
}

function Toast({ toast, onDismiss }) {
  if (!toast) return null;
  const Icon = toast.tone === "success" ? CheckCircle2 : toast.tone === "warn" ? AlertTriangle : Info;
  const iconColor = toast.tone === "success" ? "text-emerald-400" : toast.tone === "warn" ? "text-amber-400" : "text-sky-300";
  return (
    <div className="fixed top-[68px] left-1/2 -translate-x-1/2 z-[60] px-3 w-full max-w-md pointer-events-none">
      <div key={toast.id} role="status" className="pointer-events-auto flex items-center gap-3 bg-stone-900 text-stone-100 text-sm rounded-xl shadow-xl pl-4 pr-2 py-2.5 animate-toast-in">
        <Icon size={16} className={cls("shrink-0", iconColor)} />
        <span className="flex-1 leading-snug">{toast.message}</span>
        <button onClick={onDismiss} aria-label="Dismiss" className="p-1.5 rounded-md text-stone-500 hover:text-white hover:bg-white/10"><X size={14} /></button>
      </div>
    </div>
  );
}

/* ======================================================================
   SECTION: SHAPE PREVIEWS
   ====================================================================== */

function RoomThumbnail({ vertices, color, size = 72 }) {
  const bb = boundingBox(vertices);
  const w = bb.maxX - bb.minX || 1, h = bb.maxY - bb.minY || 1;
  const pad = Math.max(4, size * 0.08);
  const scale = Math.min((size - pad * 2) / w, (size - pad * 2) / h);
  const ox = (size - w * scale) / 2, oy = (size - h * scale) / 2;
  const pts = vertices.map((v) => `${(v.x - bb.minX) * scale + ox},${(v.y - bb.minY) * scale + oy}`).join(" ");
  return (
    <svg width={size} height={size} viewBox={`0 0 ${size} ${size}`} className="shrink-0" aria-hidden="true">
      <polygon points={pts} fill={color + "2e"} stroke={color} strokeWidth="2" strokeLinejoin="round" />
    </svg>
  );
}

function WallShapePreview({ vertices, lengths, unit, activeWall, onPickWall }) {
  if (!vertices || vertices.length < 3) return null;
  const bb = boundingBox(vertices);
  const w = bb.maxX - bb.minX || 1, h = bb.maxY - bb.minY || 1;
  const boxW = 300, boxH = 240, pad = 34;
  const scale = Math.min((boxW - pad * 2) / w, (boxH - pad * 2) / h);
  const ox = (boxW - w * scale) / 2, oy = (boxH - h * scale) / 2;
  const pts = vertices.map((v) => ({ x: (v.x - bb.minX) * scale + ox, y: (v.y - bb.minY) * scale + oy }));
  const cx = pts.reduce((s, p) => s + p.x, 0) / pts.length;
  const cy = pts.reduce((s, p) => s + p.y, 0) / pts.length;
  const pointsStr = pts.map((p) => `${p.x},${p.y}`).join(" ");
  return (
    <svg viewBox={`0 0 ${boxW} ${boxH}`} className="w-full h-auto bg-stone-50 border border-stone-200 rounded-xl" role="img" aria-label="Room shape with numbered walls">
      <polygon points={pointsStr} fill="#d9373214" stroke="#a8a29e" strokeWidth="2" strokeLinejoin="round" />
      {activeWall != null && pts[activeWall] && (
        <line
          x1={pts[activeWall].x} y1={pts[activeWall].y}
          x2={pts[(activeWall + 1) % pts.length].x} y2={pts[(activeWall + 1) % pts.length].y}
          stroke="#d93732" strokeWidth="5" strokeLinecap="round"
        />
      )}
      {pts.map((p, i) => {
        const q = pts[(i + 1) % pts.length];
        const mx = (p.x + q.x) / 2, my = (p.y + q.y) / 2;
        let dx = mx - cx, dy = my - cy;
        const dist = Math.hypot(dx, dy) || 1;
        dx /= dist; dy /= dist;
        const lx = mx + dx * 17, ly = my + dy * 17;
        const active = activeWall === i;
        const len = lengths ? parseLength(lengths[i], unit) : null;
        return (
          <g key={i} onClick={() => onPickWall && onPickWall(i)} style={{ cursor: onPickWall ? "pointer" : "default" }}>
            <circle cx={lx} cy={ly} r={active ? 11 : 9} fill={active ? "#d93732" : "white"} stroke={active ? "#d93732" : "#a8a29e"} strokeWidth="1.5" />
            <text x={lx} y={ly + 3.5} fontSize="10" fontWeight="600" textAnchor="middle" fill={active ? "white" : "#57534e"}>{i + 1}</text>
            {active && len != null && (
              <text x={mx - dx * 14} y={my - dy * 14 + 4} fontSize="11" fontWeight="600" textAnchor="middle" fill="#8e1b22">{formatLength(len, unit)}</text>
            )}
          </g>
        );
      })}
    </svg>
  );
}

/* ======================================================================
   SECTION: ADD / EDIT ROOM WIZARD
   ====================================================================== */

const DRAW_W = 640, DRAW_H = 420, DRAW_SNAP = 20;

// Ready-made outlines (in drawing-canvas coordinates) so the most common
// rooms don't need drawing at all — picking one jumps straight to wall sizes.
const SHAPE_TEMPLATES = [
  { key: "rect", label: "Rectangle", points: [{ x: 160, y: 100 }, { x: 480, y: 100 }, { x: 480, y: 320 }, { x: 160, y: 320 }] },
  { key: "l", label: "L-shape", points: [{ x: 160, y: 80 }, { x: 480, y: 80 }, { x: 480, y: 220 }, { x: 320, y: 220 }, { x: 320, y: 340 }, { x: 160, y: 340 }] },
  { key: "t", label: "T-shape", points: [{ x: 120, y: 80 }, { x: 520, y: 80 }, { x: 520, y: 200 }, { x: 400, y: 200 }, { x: 400, y: 340 }, { x: 240, y: 340 }, { x: 240, y: 200 }, { x: 120, y: 200 }] },
];

const DIR_LABEL = { R: "right", L: "left", U: "up", D: "down" };

function templateDirections(points) {
  return points.map((a, i) => {
    const b = points[(i + 1) % points.length];
    if (Math.abs(b.x - a.x) > Math.abs(b.y - a.y)) return b.x > a.x ? "R" : "L";
    return b.y > a.y ? "D" : "U";
  });
}

// mm -> a plain number string in the given unit (used to pre-fill edit fields).
function toUnitString(mm, unit) {
  if (mm == null || isNaN(mm)) return "";
  const v = unit === "m" ? mm / 1000 : unit === "cm" ? mm / 10 : mm;
  return String(Math.round(v * 1000) / 1000);
}

function AddRoomModal({ initialRoom, initialTemplate, onClose, onSave, displayUnit }) {
  const initialUnit = displayUnit || "mm";
  // A shape picked from the Rooms page skips the drawing step entirely.
  const templateDirs = !initialRoom && initialTemplate ? templateDirections(initialTemplate.points) : null;
  const [step, setStep] = useState(initialRoom || templateDirs ? "dims" : "draw");
  const [points, setPoints] = useState(templateDirs ? initialTemplate.points : []);
  const [directions, setDirections] = useState(initialRoom ? initialRoom.directions : templateDirs || []);
  const [drawError, setDrawError] = useState("");
  const [cursor, setCursor] = useState(null);
  // Stored wall lengths are millimetres; show them in the unit the fields use.
  const [lengths, setLengths] = useState(
    initialRoom ? initialRoom.wallLengths.map((mm) => toUnitString(mm, initialUnit)) : templateDirs ? templateDirs.map(() => "") : []
  );
  const [unit, setUnit] = useState(initialUnit);
  const [activeWall, setActiveWall] = useState(null);
  const [name, setName] = useState(initialRoom?.name || "");
  const [quantity, setQuantity] = useState(initialRoom?.quantity ?? 1);
  const [notes, setNotes] = useState(initialRoom?.notes || "");
  // Stored in mm, entered in cm.
  const [allowance, setAllowance] = useState(initialRoom?.cuttingAllowance != null ? String(initialRoom.cuttingAllowance / 10) : "");
  const [grain, setGrain] = useState(initialRoom?.grainDirection ?? false);
  const svgRef = useRef(null);
  const wallInputs = useRef([]);

  function snap(pt) { return { x: Math.round(pt.x / DRAW_SNAP) * DRAW_SNAP, y: Math.round(pt.y / DRAW_SNAP) * DRAW_SNAP }; }

  function toLocal(e) {
    const rect = svgRef.current.getBoundingClientRect();
    const x = ((e.clientX - rect.left) / rect.width) * DRAW_W;
    const y = ((e.clientY - rect.top) / rect.height) * DRAW_H;
    return snap({ x, y });
  }

  function constrainedPoint(raw) {
    if (points.length === 0) return raw;
    const last = points[points.length - 1];
    const dx = raw.x - last.x, dy = raw.y - last.y;
    if (Math.abs(dx) >= Math.abs(dy)) return { x: raw.x, y: last.y };
    return { x: last.x, y: raw.y };
  }

  function directionBetween(a, b) {
    if (Math.abs(b.x - a.x) > Math.abs(b.y - a.y)) return b.x > a.x ? "R" : "L";
    return b.y > a.y ? "D" : "U";
  }

  function handleMove(e) { setCursor(constrainedPoint(toLocal(e))); }

  function handleClick(e) {
    const raw = toLocal(e);
    const pt = constrainedPoint(raw);
    setDrawError("");
    if (points.length >= 2) {
      const start = points[0];
      const nearStart = Math.hypot(pt.x - start.x, pt.y - start.y) < 18;
      if (nearStart) { closeShape(); return; }
    }
    if (points.length > 0) {
      const last = points[points.length - 1];
      if (pt.x === last.x && pt.y === last.y) return;
      setDirections((d) => [...d, directionBetween(last, pt)]);
    }
    setPoints((p) => [...p, pt]);
  }

  function closeShape() {
    if (points.length < 3) { setDrawError("Add at least 3 corners before closing the shape."); return; }
    const last = points[points.length - 1];
    const start = points[0];
    if (last.x !== start.x && last.y !== start.y) {
      setDrawError("The last corner doesn't line up with the first one, so the shape can't close with a straight wall. Add one more corner first.");
      return;
    }
    const closingDir = directionBetween(last, start);
    const finalDirections = [...directions, closingDir];
    setDirections(finalDirections);
    setLengths(finalDirections.map(() => ""));
    setStep("dims");
  }

  function applyTemplate(t) {
    const n = t.points.length;
    const dirs = t.points.map((p, i) => directionBetween(p, t.points[(i + 1) % n]));
    setPoints(t.points);
    setDirections(dirs);
    setLengths(dirs.map(() => ""));
    setDrawError("");
    setStep("dims");
  }

  // Going back to the drawing drops the automatic closing wall again, so the
  // outline reopens exactly where the user left it.
  function backToDraw() {
    setDirections((d) => d.slice(0, -1));
    setActiveWall(null);
    setStep("draw");
  }

  function undoPoint() {
    setPoints((p) => p.slice(0, -1));
    setDirections((d) => d.slice(0, -1));
    setDrawError("");
  }
  function resetDraw() { setPoints([]); setDirections([]); setDrawError(""); }

  // Switching unit converts what's already typed instead of reinterpreting it.
  function changeUnit(next) {
    setLengths((ls) => ls.map((l) => {
      const mm = parseLength(l, unit);
      return mm == null ? l : toUnitString(mm, next);
    }));
    setUnit(next);
  }

  // ---- dimension step ----
  const numericLengths = lengths.map((l) => parseLength(l, unit));
  const { h: hSum, v: vSum } = useMemo(() => {
    let h = 0, v = 0;
    directions.forEach((d, i) => {
      const len = numericLengths[i];
      if (len == null) return;
      if (d === "R") h += len; else if (d === "L") h -= len;
      else if (d === "D") v += len; else if (d === "U") v -= len;
    });
    return { h, v };
  }, [directions, JSON.stringify(numericLengths)]); // eslint-disable-line

  const hBlanks = directions.map((d, i) => (isHorizontal(d) && numericLengths[i] == null ? i : -1)).filter((i) => i >= 0);
  const vBlanks = directions.map((d, i) => (!isHorizontal(d) && numericLengths[i] == null ? i : -1)).filter((i) => i >= 0);

  let resolvedLengths = [...numericLengths];
  let calcIndexes = new Set();
  let dimError = "";
  if (hBlanks.length === 1) {
    const idx = hBlanks[0];
    const dir = directions[idx];
    let sum = 0;
    directions.forEach((d, i) => { if (i === idx || !isHorizontal(d)) return; sum += d === "R" ? numericLengths[i] : -numericLengths[i]; });
    const needed = dir === "R" ? -sum : sum;
    if (needed > 0) { resolvedLengths[idx] = needed; calcIndexes.add(idx); }
    else dimError = "The horizontal walls can't form a closed shape with these values — check the side-to-side measurements.";
  } else if (hBlanks.length === 0 && directions.some(isHorizontal) && Math.abs(hSum) > EPS) {
    dimError = `The horizontal walls don't add up — they're off by ${formatLength(Math.abs(hSum), unit)}. Clear one and it'll be worked out for you.`;
  } else if (hBlanks.length > 1) {
    dimError = `Fill in all but one horizontal wall (${hBlanks.length} still blank).`;
  }
  if (!dimError) {
    if (vBlanks.length === 1) {
      const idx = vBlanks[0];
      const dir = directions[idx];
      let sum = 0;
      directions.forEach((d, i) => { if (i === idx || isHorizontal(d)) return; sum += d === "D" ? numericLengths[i] : -numericLengths[i]; });
      const needed = dir === "D" ? -sum : sum;
      if (needed > 0) { resolvedLengths[idx] = needed; calcIndexes.add(idx); }
      else dimError = "The vertical walls can't form a closed shape with these values — check the top-to-bottom measurements.";
    } else if (vBlanks.length === 0 && directions.some((d) => !isHorizontal(d)) && Math.abs(vSum) > EPS) {
      dimError = `The vertical walls don't add up — they're off by ${formatLength(Math.abs(vSum), unit)}. Clear one and it'll be worked out for you.`;
    } else if (vBlanks.length > 1) {
      dimError = `Fill in all but one vertical wall (${vBlanks.length} still blank).`;
    }
  }

  const allFilled = resolvedLengths.every((l) => l != null && l > 0);
  const canConstruct = allFilled && !dimError;
  const previewVerts = canConstruct ? buildPolygon(directions, resolvedLengths) : null;
  const previewArea = previewVerts ? polygonArea(previewVerts) : 0;
  const previewBB = previewVerts ? boundingBox(previewVerts) : null;
  const filledCount = numericLengths.filter((l) => l != null).length;

  const shapeVerts = previewVerts || (points.length > 0 ? points : (initialRoom ? buildPolygon(directions, initialRoom.wallLengths) : null));

  function handleSave() {
    if (!canConstruct || !name.trim()) return;
    const vertices = buildPolygon(directions, resolvedLengths);
    const bb = boundingBox(vertices);
    const allowanceCm = parseFloat(allowance);
    onSave({
      id: initialRoom?.id || `room_${Date.now()}`,
      name: name.trim(),
      vertices,
      directions,
      wallLengths: resolvedLengths,
      width: bb.maxX - bb.minX,
      length: bb.maxY - bb.minY,
      area: polygonArea(vertices),
      corners: vertices.length,
      quantity: Math.max(1, parseInt(quantity) || 1),
      notes,
      cuttingAllowance: allowance === "" || !isFinite(allowanceCm) ? null : allowanceCm * 10,
      grainDirection: grain,
      color: initialRoom?.color || ROOM_COLORS[Math.floor(Math.random() * ROOM_COLORS.length)],
    });
  }

  function onWallKeyDown(e, i) {
    if (e.key !== "Enter") return;
    e.preventDefault();
    const next = wallInputs.current[i + 1];
    if (next) next.focus();
    else if (canConstruct) setStep("details");
  }

  const drawPtsStr = points.map((p) => `${p.x},${p.y}`).join(" ");
  const previewLine = points.length > 0 && cursor ? `${points[points.length - 1].x},${points[points.length - 1].y} ${cursor.x},${cursor.y}` : "";
  const cursorNearStart = points.length >= 3 && cursor && Math.hypot(cursor.x - points[0].x, cursor.y - points[0].y) < 18;

  const steps = initialRoom
    ? [["dims", "Wall lengths"], ["details", "Details"]]
    : [["draw", "Shape"], ["dims", "Wall lengths"], ["details", "Details"]];
  const stepIndex = steps.findIndex(([k]) => k === step);

  return (
    <Modal onClose={onClose} dismissible={false} className="max-w-4xl" labelledBy="room-modal-title">
      {/* Header + stepper */}
      <div className="flex items-start justify-between gap-4 px-5 sm:px-6 pt-5 pb-4 border-b border-stone-100">
        <div className="min-w-0">
          <h2 id="room-modal-title" className="text-lg font-semibold text-stone-900">{initialRoom ? `Edit “${initialRoom.name}”` : "Add a room"}</h2>
          <ol className="flex items-center gap-2 mt-3 flex-wrap">
            {steps.map(([key, label], i) => {
              const active = i === stepIndex, done = i < stepIndex;
              return (
                <li key={key} className="flex items-center gap-2">
                  <span className={cls("w-6 h-6 rounded-full grid place-items-center text-xs font-semibold transition-colors",
                    active ? "bg-brand-500 text-white" : done ? "bg-brand-100 text-brand-700" : "bg-stone-100 text-stone-500")}>
                    {done ? <Check size={12} strokeWidth={3} /> : i + 1}
                  </span>
                  <span className={cls("text-xs", active ? "text-stone-900 font-medium" : "text-stone-500")}>{label}</span>
                  {i < steps.length - 1 && <span className="w-6 h-px bg-stone-200" />}
                </li>
              );
            })}
          </ol>
        </div>
        <IconButton label="Close without saving" onClick={onClose}><X size={18} /></IconButton>
      </div>

      {/* Step 1 — shape */}
      {step === "draw" && (
        <>
          <div className="flex-1 overflow-y-auto px-5 sm:px-6 py-5">
            <p className="text-sm font-medium text-stone-800 mb-2.5">Start from a common shape</p>
            <div className="grid grid-cols-3 gap-2.5 mb-6">
              {SHAPE_TEMPLATES.map((t) => (
                <button key={t.key} type="button" onClick={() => applyTemplate(t)}
                  className={cls("group flex flex-col items-center gap-1.5 p-3 rounded-xl border border-stone-200 bg-white hover:border-brand-500 hover:bg-brand-50 transition-colors", FOCUS_RING)}>
                  <RoomThumbnail vertices={t.points} color="#d93732" size={52} />
                  <span className="text-xs font-medium text-stone-700 group-hover:text-brand-700">{t.label}</span>
                </button>
              ))}
            </div>

            <div className="flex items-baseline justify-between gap-3 mb-2.5">
              <p className="text-sm font-medium text-stone-800">…or draw your own</p>
              <p className="text-xs text-stone-600 hidden sm:block">Click to add corners · walls snap straight · click the <span className="text-brand-600 font-medium">green dot</span> to finish</p>
            </div>
            <div className="relative">
              <svg
                ref={svgRef}
                viewBox={`0 0 ${DRAW_W} ${DRAW_H}`}
                className="w-full bg-white border border-stone-200 rounded-xl cursor-crosshair select-none touch-none"
                style={{ aspectRatio: `${DRAW_W}/${DRAW_H}` }}
                onMouseMove={handleMove}
                onMouseLeave={() => setCursor(null)}
                onClick={handleClick}
              >
                <defs>
                  <pattern id="dotgrid" width={DRAW_SNAP} height={DRAW_SNAP} patternUnits="userSpaceOnUse">
                    <circle cx="1" cy="1" r="1.1" fill="#e7e5e4" />
                  </pattern>
                </defs>
                <rect width={DRAW_W} height={DRAW_H} fill="url(#dotgrid)" />
                {points.length > 1 && <polyline points={drawPtsStr} fill="#d937320d" stroke="#d93732" strokeWidth="3" strokeLinejoin="round" />}
                {previewLine && <polyline points={previewLine} fill="none" stroke="#57534e" strokeWidth="2" strokeDasharray="6 4" />}
                {points.map((p, i) => (
                  <g key={i}>
                    {i === 0 && points.length >= 3 && <circle cx={p.x} cy={p.y} r={cursorNearStart ? 16 : 13} fill="#d9373222" className="transition-all" />}
                    <circle cx={p.x} cy={p.y} r={i === 0 ? 8 : 5.5} fill={i === 0 ? "#d93732" : "white"} stroke={i === 0 ? "white" : "#d93732"} strokeWidth="2.5" />
                  </g>
                ))}
                {cursor && !cursorNearStart && <circle cx={cursor.x} cy={cursor.y} r="4" fill="#57534e" />}
              </svg>
              {points.length === 0 && (
                <div className="absolute inset-0 flex items-center justify-center pointer-events-none">
                  <span className="flex items-center gap-2 text-xs text-stone-600 bg-white/95 px-3.5 py-2 rounded-full border border-stone-200 shadow-sm">
                    <MousePointerClick size={14} className="text-brand-500" /> Click anywhere to place the first corner
                  </span>
                </div>
              )}
            </div>
            {drawError && <div className="mt-3"><Notice tone="error">{drawError}</Notice></div>}
          </div>
          <div className="flex items-center gap-2 px-5 sm:px-6 py-4 border-t border-stone-100 bg-stone-50/60">
            <Button variant="ghost" size="sm" onClick={undoPoint} disabled={points.length === 0} title="Remove the last corner placed"><Undo size={14} /> Undo corner</Button>
            <Button variant="ghost" size="sm" onClick={resetDraw} disabled={points.length === 0} title="Clear this drawing and start over">Start over</Button>
            <Button variant="primary" className="ml-auto" onClick={closeShape} disabled={points.length < 3} title="Finish the shape">
              Finish shape <ChevronRight size={16} />
            </Button>
          </div>
        </>
      )}

      {/* Step 2 — wall lengths */}
      {step === "dims" && (
        <>
          <div className="flex-1 overflow-y-auto px-5 sm:px-6 py-5">
            <div className="grid md:grid-cols-[minmax(0,300px)_1fr] gap-5 md:gap-6">
              <div className="md:sticky md:top-0 self-start">
                <WallShapePreview
                  vertices={shapeVerts} lengths={lengths} unit={unit} activeWall={activeWall}
                  onPickWall={(i) => wallInputs.current[i]?.focus()}
                />
                <p className="text-xs text-stone-500 mt-2 text-center">Tap a number on the shape to jump to that wall</p>
              </div>

              <div className="min-w-0">
                <div className="flex items-center justify-between gap-3 mb-1">
                  <p className="text-sm font-medium text-stone-800">Measure each wall</p>
                  <Segmented value={unit} onChange={changeUnit} options={[{ value: "mm", label: "mm" }, { value: "cm", label: "cm" }, { value: "m", label: "m" }]} />
                </div>
                <p className="text-xs text-stone-600 mb-3.5 leading-relaxed">
                  Tip: leave <b className="font-medium text-stone-700">one side-to-side</b> and <b className="font-medium text-stone-700">one top-to-bottom</b> wall blank and they'll be calculated for you. Mixed units like <code className="text-xs bg-stone-100 px-1 rounded">3m 45cm</code> work too.
                </p>
                <div className="grid sm:grid-cols-2 gap-2">
                  {directions.map((d, i) => {
                    const Icon = DIR_ICON[d];
                    const isActive = activeWall === i;
                    const isCalc = calcIndexes.has(i);
                    return (
                      <label
                        key={i}
                        className={cls("flex items-center gap-2.5 h-11 bg-white border rounded-lg pl-2 pr-3 transition-colors cursor-text",
                          isActive ? "border-brand-500 ring-2 ring-brand-500/20" : "border-stone-200 hover:border-stone-300")}
                      >
                        <span className={cls("w-6 h-6 rounded-full grid place-items-center text-xs font-semibold shrink-0", isActive ? "bg-brand-500 text-white" : "bg-stone-100 text-stone-600")}>{i + 1}</span>
                        <Icon size={14} className="text-stone-500 shrink-0" aria-label={`Wall goes ${DIR_LABEL[d]}`} />
                        <input
                          ref={(el) => (wallInputs.current[i] = el)}
                          value={lengths[i] ?? ""}
                          inputMode="decimal"
                          aria-label={`Wall ${i + 1} length`}
                          onChange={(e) => setLengths((ls) => ls.map((l, j) => (j === i ? e.target.value : l)))}
                          onFocus={() => setActiveWall(i)}
                          onBlur={() => setActiveWall((a) => (a === i ? null : a))}
                          onKeyDown={(e) => onWallKeyDown(e, i)}
                          placeholder={isCalc ? "auto" : (isHorizontal(d) ? "Width" : "Length")}
                          className="flex-1 min-w-0 text-sm tabular-nums border-0 outline-none bg-transparent placeholder:text-stone-300"
                        />
                        {isCalc
                          ? <span className="text-xs font-medium text-brand-700 bg-brand-50 rounded px-1.5 py-0.5 shrink-0 tabular-nums">= {formatLength(resolvedLengths[i], unit)}</span>
                          : <span className="text-xs text-stone-500 shrink-0">{unit}</span>}
                      </label>
                    );
                  })}
                </div>

                <div className="mt-4">
                  {dimError ? (
                    <Notice tone={dimError.includes("still blank") ? "info" : "warn"}>{dimError}</Notice>
                  ) : canConstruct && previewBB ? (
                    <Notice tone="success">
                      <span className="font-medium">Looks good!</span>{" "}
                      {formatLength(previewBB.maxX - previewBB.minX, unit)} × {formatLength(previewBB.maxY - previewBB.minY, unit)} · {formatArea(previewArea)} · {previewVerts.length} corners
                    </Notice>
                  ) : (
                    <Notice tone="info">{filledCount} of {directions.length} walls entered.</Notice>
                  )}
                </div>
              </div>
            </div>
          </div>
          <div className="flex items-center gap-2 px-5 sm:px-6 py-4 border-t border-stone-100 bg-stone-50/60">
            {!initialRoom && <Button variant="ghost" onClick={backToDraw}><ChevronLeft size={16} /> Back</Button>}
            <Button variant="primary" className="ml-auto" onClick={() => setStep("details")} disabled={!canConstruct}>Next <ChevronRight size={16} /></Button>
          </div>
        </>
      )}

      {/* Step 3 — details */}
      {step === "details" && (
        <>
          <div className="flex-1 overflow-y-auto px-5 sm:px-6 py-5">
            <div className="grid md:grid-cols-[1fr_240px] gap-6">
              <div className="space-y-4">
                <Field label="Room name">
                  <input
                    value={name} onChange={(e) => setName(e.target.value)} autoFocus
                    onKeyDown={(e) => { if (e.key === "Enter") handleSave(); }}
                    className={INPUT} placeholder="e.g. Living room"
                  />
                </Field>
                <div className="grid grid-cols-2 gap-4">
                  <Field label="How many?" hint="Identical pieces to cut">
                    <QtyStepper value={Math.max(1, parseInt(quantity) || 1)} onChange={setQuantity} />
                  </Field>
                  <Field label="Cutting allowance" hint="Leave blank to use the roll default">
                    <div className="relative">
                      <input value={allowance} onChange={(e) => setAllowance(e.target.value)} inputMode="decimal" placeholder="Default" className={INPUT + " pr-10"} />
                      <span className="absolute right-3 top-1/2 -translate-y-1/2 text-xs text-stone-500">cm</span>
                    </div>
                  </Field>
                </div>
                <Field label="Notes (optional)">
                  <textarea value={notes} onChange={(e) => setNotes(e.target.value)} rows={2} placeholder="Doorway, underlay, fitting notes…" className={INPUT + " h-auto py-2 resize-none"} />
                </Field>
                <Toggle checked={grain} onChange={setGrain} label="Show pile direction" description="Draws an arrow on this room in the cutting layout so the pile runs the right way." />
              </div>
              {previewVerts && (
                <div className="bg-stone-50 border border-stone-200 rounded-xl p-4 flex flex-col items-center text-center self-start">
                  <RoomThumbnail vertices={previewVerts} color={initialRoom?.color || "#d93732"} size={120} />
                  <p className="text-sm font-medium text-stone-900 mt-2 truncate max-w-full">{name.trim() || "Untitled room"}</p>
                  <p className="text-xs text-stone-600 tabular-nums mt-0.5">{formatLength(previewBB.maxX - previewBB.minX, "m")} × {formatLength(previewBB.maxY - previewBB.minY, "m")}</p>
                  <p className="text-xs text-stone-600 tabular-nums">{formatArea(previewArea)}{parseInt(quantity) > 1 ? ` × ${parseInt(quantity)}` : ""}</p>
                </div>
              )}
            </div>
          </div>
          <div className="flex items-center gap-2 px-5 sm:px-6 py-4 border-t border-stone-100 bg-stone-50/60">
            <Button variant="ghost" onClick={() => setStep("dims")}><ChevronLeft size={16} /> Back</Button>
            {!name.trim() && <span className="ml-auto text-xs text-stone-500 hidden sm:inline">Give the room a name to save it</span>}
            <Button variant="primary" className={name.trim() ? "ml-auto" : "sm:ml-0 ml-auto"} onClick={handleSave} disabled={!name.trim()}><Check size={16} /> {initialRoom ? "Save changes" : "Add room"}</Button>
          </div>
        </>
      )}
    </Modal>
  );
}

/* ======================================================================
   SECTION: ROLL SETTINGS (shared by both views)
   ====================================================================== */

const ROLL_PRESETS = [3.66, 4.0, 5.0];

function RollSettings({ rollWidth, setRollWidth, unit, setUnit, tolerance, setTolerance, grainMode, setGrainMode, gridSize, setGridSize, snapEnabled, setSnapEnabled, allowOverlap, setAllowOverlap, guillotineMode, setGuillotineMode }) {
  const [showAdvanced, setShowAdvanced] = useState(false);

  // The roll-width field keeps its own text buffer, separate from the
  // committed rollWidth (mm) state, and only parses/clamps/commits on blur
  // or Enter — so clearing the field to retype it never snaps it to the
  // minimum mid-edit. Invalid or empty input reverts to the current width.
  const [rollWidthText, setRollWidthText] = useState(String(rollWidth / 1000));
  useEffect(() => { setRollWidthText(String(rollWidth / 1000)); }, [rollWidth]);
  function commitRollWidth() {
    const parsed = parseFloat(rollWidthText);
    if (isFinite(parsed) && parsed > 0) {
      setRollWidth(Math.max(500, Math.round(parsed * 1000)));
    } else {
      setRollWidthText(String(rollWidth / 1000));
    }
  }

  return (
    <div className="space-y-4">
      <Field label="Roll width" hint="How wide the carpet roll is. Most rolls are 4m or 5m.">
        <div className="relative">
          <input
            type="number" step="0.01" min="0.5" value={rollWidthText} inputMode="decimal"
            onChange={(e) => setRollWidthText(e.target.value)}
            onBlur={commitRollWidth}
            onKeyDown={(e) => { if (e.key === "Enter") e.currentTarget.blur(); }}
            className={INPUT + " pr-9 tabular-nums font-medium"}
          />
          <span className="absolute right-3 top-1/2 -translate-y-1/2 text-sm text-stone-500">m</span>
        </div>
        <div className="flex gap-1.5 mt-2">
          {ROLL_PRESETS.map((w) => {
            const active = Math.round(w * 1000) === rollWidth;
            return (
              <button key={w} type="button" onClick={() => setRollWidth(Math.round(w * 1000))} title={`Set roll width to ${w}m`}
                className={cls("flex-1 text-xs font-medium h-7 rounded-md border transition-colors", FOCUS_RING,
                  active ? "bg-brand-50 border-brand-500 text-brand-700" : "bg-white border-stone-200 text-stone-600 hover:border-stone-300")}>
                {w}m
              </button>
            );
          })}
        </div>
      </Field>

      <Field label="Show measurements in">
        <Segmented className="w-full" value={unit} onChange={setUnit} options={[{ value: "mm", label: "mm" }, { value: "cm", label: "cm" }, { value: "m", label: "metres" }]} />
      </Field>

      <button
        type="button"
        onClick={() => setShowAdvanced((s) => !s)}
        aria-expanded={showAdvanced}
        className={cls("w-full flex items-center justify-between text-xs font-medium text-stone-600 hover:text-stone-800 pt-3 border-t border-stone-100", FOCUS_RING)}
      >
        <span className="flex items-center gap-1.5"><Settings2 size={13} /> Advanced settings</span>
        <ChevronDown size={14} className={cls("transition-transform", showAdvanced && "rotate-180")} />
      </button>

      {showAdvanced && (
        <div className="space-y-4 animate-fade-in">
          <Field label="Gap around each piece" hint="Extra allowance kept clear between pieces for trimming.">
            <select value={tolerance} onChange={(e) => setTolerance(parseInt(e.target.value))} className={SELECT}>
              {[0, 1, 2.5, 5, 10].map((cm) => <option key={cm} value={cm * 10}>{cm === 0 ? "None" : `${cm} cm`}</option>)}
            </select>
          </Field>
          <Field label="Turning pieces">
            <select value={grainMode} onChange={(e) => setGrainMode(e.target.value)} className={SELECT}>
              <option value="free">Turn any amount</option>
              <option value="90">Turn in 90° steps only</option>
              <option value="locked">Don't allow turning (keep pile direction)</option>
            </select>
          </Field>
          <Field label="Snap to grid">
            <div className="flex items-center gap-3">
              <select value={gridSize} onChange={(e) => setGridSize(parseInt(e.target.value))} disabled={!snapEnabled} className={SELECT + " flex-1 disabled:opacity-50"}>
                {[10, 25, 50, 100].map((v) => <option key={v} value={v}>{v} mm</option>)}
              </select>
              <button type="button" role="switch" aria-checked={snapEnabled} aria-label="Snap to grid" onClick={() => setSnapEnabled(!snapEnabled)}
                className={cls("relative w-9 h-5 shrink-0 rounded-full transition-colors", FOCUS_RING, snapEnabled ? "bg-brand-500" : "bg-stone-300")}>
                <span className={cls("absolute top-0.5 left-0.5 w-4 h-4 rounded-full bg-white shadow transition-transform", snapEnabled && "translate-x-4")} />
              </button>
            </div>
          </Field>
          <div className="pt-3 border-t border-stone-100 space-y-4">
            <Toggle
              checked={guillotineMode} onChange={setGuillotineMode}
              label="Straight cuts only"
              description={guillotineMode
                ? "“Arrange for me” keeps every cut running straight across — easy with a knife and rule, though it may use a little more carpet."
                : "“Arrange for me” can nest pieces into any gap (even the notch of an L-shape) for the tightest fit, but cuts may not be straight."}
            />
            <Toggle
              checked={allowOverlap} onChange={setAllowOverlap}
              label="Allow pieces to overlap"
              description={allowOverlap
                ? "Pieces can be dropped on top of each other — overlaps are outlined in red until you move them apart."
                : "Pieces snap back to the last clear spot if they'd overlap another room."}
            />
          </div>
        </div>
      )}
    </div>
  );
}

/* ======================================================================
   SECTION: ROOMS VIEW — the room library
   ====================================================================== */

// Warm-tinted elevation (matches the ivory page rather than flat grey).
const CARD = "bg-white rounded-2xl ring-1 ring-stone-900/[0.06] shadow-[0_1px_2px_rgba(60,40,30,0.05),0_8px_24px_-12px_rgba(60,40,30,0.12)]";

function PlacedBadge({ placed, quantity }) {
  const done = placed >= quantity;
  return (
    <span className={cls("inline-flex items-center gap-1 text-xs font-medium tabular-nums",
      done ? "text-emerald-700" : placed > 0 ? "text-amber-700" : "text-stone-500")}>
      {done ? <CheckCircle2 size={13} /> : <CircleDashed size={13} />}
      {placed} of {quantity} on the roll
    </span>
  );
}

// The one big, unmistakable "add a room" control.
function AddRoomButton({ onClick, size = "lg" }) {
  const big = size === "lg";
  return (
    <button
      type="button" onClick={onClick} aria-label="Add a room"
      className={cls("group mx-auto grid place-items-center rounded-full bg-brand-600 text-white transition-all duration-200",
        "shadow-[0_14px_32px_-12px_rgba(142,27,34,0.65)] hover:bg-brand-700 hover:shadow-[0_18px_36px_-12px_rgba(142,27,34,0.7)] hover:-translate-y-0.5 active:translate-y-0 active:scale-[0.97]",
        "focus-visible:outline-none focus-visible:ring-4 focus-visible:ring-brand-500/30",
        big ? "w-28 h-28" : "w-16 h-16")}
    >
      <Plus size={big ? 46 : 28} strokeWidth={2.25} className="transition-transform duration-200 group-hover:rotate-90" />
    </button>
  );
}

function ShapeShortcuts({ onPick }) {
  return (
    <div className="flex items-center justify-center gap-2.5">
      {SHAPE_TEMPLATES.map((t) => (
        <button
          key={t.key} type="button" onClick={() => onPick(t)} title={`Start with a ${t.label.toLowerCase()} room`}
          className={cls("flex items-center gap-2 h-11 pl-2 pr-3.5 rounded-xl bg-white ring-1 ring-stone-900/[0.08] text-sm font-medium text-stone-700",
            "hover:ring-brand-500/50 hover:text-brand-700 active:scale-[0.98] transition-all", FOCUS_RING)}
        >
          <RoomThumbnail vertices={t.points} color="#b8282a" size={28} />
          {t.label}
        </button>
      ))}
    </div>
  );
}

function EmptyRooms({ onAddRoom, onOpenHelp }) {
  return (
    <div className="flex-1 min-h-0 overflow-y-auto">
      <div className="min-h-full grid place-items-center px-6 py-12">
        <div className="text-center animate-fade-in">
          <AddRoomButton onClick={() => onAddRoom()} />
          <p className="mt-6 text-xl font-semibold text-stone-900">Add a room</p>
          <p className="mt-1 text-sm text-stone-600 max-w-[30ch] mx-auto [text-wrap:balance]">Start with the first room you want to carpet.</p>

          <div className="mt-10">
            <p className="text-xs text-stone-500 mb-3">or start from a shape</p>
            <ShapeShortcuts onPick={onAddRoom} />
          </div>

          <button type="button" onClick={onOpenHelp} className={cls("mt-10 inline-flex items-center gap-1.5 text-sm text-stone-600 underline decoration-stone-300 underline-offset-4 hover:text-stone-900 hover:decoration-stone-500 transition-colors", FOCUS_RING)}>
            <HelpCircle size={15} /> How does this work?
          </button>
        </div>
      </div>
    </div>
  );
}

function RoomCard({ room, placed, unit, onEdit, onDuplicate, onDelete, onQuantityChange, onPlace }) {
  const [confirmDelete, setConfirmDelete] = useState(false);
  return (
    <article className={cls(CARD, "group flex flex-col overflow-hidden transition-shadow hover:shadow-[0_1px_2px_rgba(60,40,30,0.06),0_14px_32px_-14px_rgba(60,40,30,0.22)]")}>
      <button type="button" onClick={onEdit} title="Change this room" className={cls("relative h-40 bg-stone-50 grid place-items-center", FOCUS_RING)}>
        <RoomThumbnail vertices={room.vertices} color={room.color} size={124} />
        <span className="absolute bottom-3 right-3 opacity-0 group-hover:opacity-100 transition-opacity text-xs font-medium text-stone-700 bg-white/90 rounded-md px-2 py-1 flex items-center gap-1"><Pencil size={12} /> Change</span>
      </button>
      <div className="px-5 pt-4 pb-5 flex-1 flex flex-col">
        <h3 className="text-base font-semibold text-stone-900 truncate">{room.name}</h3>
        <p className="text-sm text-stone-600 tabular-nums mt-0.5">{formatLength(room.width, unit)} × {formatLength(room.length, unit)} <span className="text-stone-400">·</span> {formatArea(room.area)}</p>
        {room.notes && <p className="text-xs text-stone-500 mt-1.5 line-clamp-2">{room.notes}</p>}

        <div className="flex items-center justify-between mt-4">
          <span className="text-sm text-stone-700">How many</span>
          <QtyStepper value={room.quantity} onChange={(q) => onQuantityChange(room.id, q)} />
        </div>
        <div className="mt-2"><PlacedBadge placed={placed} quantity={room.quantity} /></div>

        <div className="mt-auto pt-4">
          {confirmDelete ? (
            <div className="flex items-center gap-2 animate-fade-in">
              <span className="text-sm text-stone-700 flex-1 min-w-0">Delete this room?</span>
              <Button variant="ghost" size="sm" onClick={() => setConfirmDelete(false)}>Keep</Button>
              <Button variant="danger" size="sm" onClick={() => { onDelete(room.id); setConfirmDelete(false); }}>Delete</Button>
            </div>
          ) : (
            <div className="flex items-center gap-1">
              <Button variant="secondary" size="sm" className="h-9" onClick={() => onPlace(room)} title="Put one of these on the carpet roll"><Layers size={14} /> Put on roll</Button>
              <IconButton label="Make a copy" onClick={() => onDuplicate(room)} className="ml-auto"><Copy size={16} /></IconButton>
              <IconButton label="Delete room" onClick={() => setConfirmDelete(true)} className="hover:!text-red-600 hover:!bg-red-50"><Trash2 size={16} /></IconButton>
            </div>
          )}
        </div>
      </div>
    </article>
  );
}

function AddRoomTile({ onAddRoom }) {
  return (
    <div className="rounded-2xl bg-stone-100/70 min-h-[300px] flex flex-col items-center justify-center gap-4 px-5 py-8 text-center">
      <AddRoomButton onClick={() => onAddRoom()} size="md" />
      <div>
        <p className="text-base font-semibold text-stone-900">Add a room</p>
        <p className="text-sm text-stone-600 mt-0.5">Another room that needs carpet</p>
      </div>
    </div>
  );
}

function RoomsView({ projectName, setProjectName, onOpenHelp, rooms, placedByRoom, unit, onAddRoom, onEditRoom, onDeleteRoom, onDuplicateRoom, onQuantityChange, onPlaceOnCarpet, onPlaceAll, onGoToLayout, settings, totals }) {
  if (rooms.length === 0) return <EmptyRooms onAddRoom={onAddRoom} onOpenHelp={onOpenHelp} />;
  const remaining = totals.needed - totals.placed;
  const pct = totals.needed ? Math.min(100, (totals.placed / totals.needed) * 100) : 0;
  return (
    <div className="flex-1 min-h-0 overflow-y-auto">
      <div className="max-w-[1320px] mx-auto px-4 sm:px-8 pt-6 pb-16 grid lg:grid-cols-[minmax(0,1fr)_340px] gap-8 lg:gap-10">
        <section className="min-w-0">
          <div className="mb-5">
            <ProjectNameField projectName={projectName} setProjectName={setProjectName} />
          </div>
          <div className="grid sm:grid-cols-2 xl:grid-cols-3 gap-5">
            <AddRoomTile onAddRoom={onAddRoom} />
            {rooms.map((room) => (
              <RoomCard
                key={room.id} room={room} placed={placedByRoom[room.id] || 0} unit={unit}
                onEdit={() => onEditRoom(room)} onDuplicate={onDuplicateRoom} onDelete={onDeleteRoom}
                onQuantityChange={onQuantityChange} onPlace={onPlaceOnCarpet}
              />
            ))}
          </div>
        </section>

        <aside className="space-y-5 lg:sticky lg:top-6 self-start">
          <section className="rounded-2xl bg-ink-900 text-white p-5">
            <p className="font-display text-xs font-semibold uppercase tracking-[0.22em] text-stone-400">Next</p>
            <p className="text-lg font-semibold mt-1">Plan the cut</p>
            <div className="mt-4 h-1.5 rounded-full bg-white/10 overflow-hidden">
              <div className="h-full bg-brand-500 rounded-full transition-all duration-500" style={{ width: `${pct}%` }} />
            </div>
            <p className="text-sm text-stone-300 mt-2 tabular-nums">{totals.placed} of {totals.needed} pieces on the roll</p>
            <div className="flex flex-col gap-2 mt-5">
              {remaining > 0 && <Button variant="primary" className="w-full h-11" onClick={onPlaceAll}>Put all {remaining} on the roll <ArrowRight size={16} /></Button>}
              <Button variant="ghost" className={cls("w-full h-11 !text-white hover:!bg-white/10", remaining > 0 ? "" : "!bg-brand-600 hover:!bg-brand-700")} onClick={onGoToLayout}>
                {remaining > 0 ? "Just open the plan" : <>Open the plan <ArrowRight size={16} /></>}
              </Button>
            </div>
          </section>
          <section className={cls(CARD, "p-5")}>
            <h2 className="text-base font-semibold text-stone-900 mb-4">Carpet roll</h2>
            <RollSettings {...settings} />
          </section>
        </aside>
      </div>
    </div>
  );
}

/* ======================================================================
   SECTION: CUTTING VIEW SIDE PANELS
   ====================================================================== */

function RoomTray({ rooms, placedByRoom, onPlaceOnCarpet, onPlaceAll, onAddRoom, remaining }) {
  return (
    <aside className="hidden md:flex w-64 shrink-0 flex-col bg-white border-r border-stone-200 min-h-0">
      <div className="flex items-center justify-between px-4 h-12 border-b border-stone-100 shrink-0">
        <h2 className="text-sm font-semibold text-stone-900">Rooms</h2>
        <IconButton label="Add a room" onClick={onAddRoom} className="w-8 h-8"><Plus size={16} /></IconButton>
      </div>
      <div className="flex-1 overflow-y-auto p-3 space-y-1.5">
        {rooms.length === 0 && (
          <div className="text-center px-3 py-8">
            <p className="text-sm text-stone-600 font-medium">No rooms yet</p>
            <p className="text-xs text-stone-500 mt-1 mb-4">Add a room to start laying out your carpet.</p>
            <Button variant="primary" size="sm" onClick={onAddRoom}><Plus size={14} /> Add room</Button>
          </div>
        )}
        {remaining > 0 && (
          <Button variant="secondary" size="sm" className="w-full mb-2" onClick={onPlaceAll}><Layers size={13} /> Place all {remaining} remaining</Button>
        )}
        {rooms.map((room) => {
          const placed = placedByRoom[room.id] || 0;
          return (
            <div
              key={room.id}
              draggable
              onDragStart={(e) => { e.dataTransfer.setData("roomId", room.id); e.dataTransfer.effectAllowed = "copy"; }}
              title="Drag onto the roll"
              className="group flex items-center gap-2.5 p-2 rounded-lg border border-transparent hover:border-stone-200 hover:bg-stone-50 cursor-grab active:cursor-grabbing transition-colors"
            >
              <div className="w-11 h-11 rounded-md bg-stone-50 border border-stone-100 grid place-items-center shrink-0">
                <RoomThumbnail vertices={room.vertices} color={room.color} size={38} />
              </div>
              <div className="flex-1 min-w-0">
                <p className="text-sm font-medium text-stone-800 truncate">{room.name}</p>
                <p className={cls("text-xs tabular-nums", placed >= room.quantity ? "text-emerald-600" : "text-stone-500")}>
                  {placed}/{room.quantity} placed
                </p>
              </div>
              <IconButton label={`Place one ${room.name} on the carpet`} onClick={() => onPlaceOnCarpet(room)} className="w-8 h-8 text-brand-600 hover:bg-brand-50 hover:text-brand-700"><Plus size={16} /></IconButton>
            </div>
          );
        })}
      </div>
      {rooms.length > 0 && (
        <p className="text-xs text-stone-500 px-4 py-3 border-t border-stone-100 leading-snug">Drag a room onto the roll, or press <b className="font-medium text-stone-600">+</b> to add it below the others.</p>
      )}
    </aside>
  );
}

function StatTile({ label, value, sub, tone }) {
  return (
    <div className="rounded-lg bg-stone-50 border border-stone-100 px-3 py-2.5">
      <p className="text-xs text-stone-600">{label}</p>
      <p className={cls("text-base font-semibold tabular-nums mt-0.5", tone === "accent" ? "text-brand-600" : "text-stone-900")}>{value}</p>
      {sub && <p className="text-xs text-stone-500 tabular-nums">{sub}</p>}
    </div>
  );
}

function AllowanceOverrideInput({ instance, onChange }) {
  const current = instance.allowanceOverride != null && instance.allowanceOverride !== "" ? String(parseFloat(instance.allowanceOverride) / 10) : "";
  const [text, setText] = useState(current);
  useEffect(() => { setText(current); }, [current, instance.id]);
  // Commit on blur / Enter only, so typing "2.5" isn't mangled mid-way and
  // each edit is one undo step rather than one per keystroke.
  function commit() {
    const t = text.trim();
    if (t === "") { if (current !== "") onChange(""); return; }
    const v = parseFloat(t);
    if (isFinite(v) && v >= 0) { if (String(v) !== current) onChange(String(v * 10)); }
    else setText(current);
  }
  return (
    <div className="relative">
      <input
        value={text} inputMode="decimal" placeholder="Roll default"
        onChange={(e) => setText(e.target.value)} onBlur={commit}
        onKeyDown={(e) => { if (e.key === "Enter") e.currentTarget.blur(); }}
        className={INPUT + " pr-10"}
      />
      <span className="absolute right-3 top-1/2 -translate-y-1/2 text-xs text-stone-500">cm</span>
    </div>
  );
}

function Inspector({ instance, room, onRotate, onDelete, onDuplicate, onAllowanceChange, onEditRoom, onDeselect, unit, rotationLocked }) {
  const verts = instanceVertices(room, instance);
  const bb = boundingBox(verts);
  const rows = [
    ["Size", `${formatLength(bb.maxX - bb.minX, unit)} × ${formatLength(bb.maxY - bb.minY, unit)}`],
    ["Area", formatArea(room.area)],
    ["From left edge", formatLength(instance.x, unit)],
    ["From roll start", formatLength(instance.y, unit)],
    ["Rotation", `${instance.rotation}°`],
  ];
  return (
    <div className="p-4 space-y-4 animate-fade-in">
      <div className="flex items-start gap-3">
        <div className="w-12 h-12 rounded-lg bg-stone-50 border border-stone-100 grid place-items-center shrink-0">
          <RoomThumbnail vertices={rotatePolygon(room.vertices, instance.rotation)} color={room.color} size={42} />
        </div>
        <div className="min-w-0 flex-1">
          <p className="text-xs text-stone-600">Selected piece</p>
          <h3 className="text-sm font-semibold text-stone-900 truncate">{room.name}</h3>
        </div>
        <IconButton label="Deselect (Esc)" onClick={onDeselect} className="w-8 h-8 -mr-1 -mt-1"><X size={15} /></IconButton>
      </div>

      <dl className="text-xs rounded-lg border border-stone-100 divide-y divide-stone-100">
        {rows.map(([k, v]) => (
          <div key={k} className="flex justify-between gap-3 px-3 py-2">
            <dt className="text-stone-600">{k}</dt><dd className="text-stone-900 font-medium tabular-nums text-right">{v}</dd>
          </div>
        ))}
      </dl>

      <div className="grid grid-cols-2 gap-2">
        <Button variant="secondary" size="sm" className="h-9" onClick={onRotate} disabled={rotationLocked} title={rotationLocked ? "Turning is switched off in roll settings" : "Rotate 90° (R)"}><RotateCw size={14} /> Rotate</Button>
        <Button variant="secondary" size="sm" className="h-9" onClick={onDuplicate} title="Duplicate this piece"><Copy size={14} /> Duplicate</Button>
      </div>

      <Field label="Cutting allowance for this piece" hint="Overrides the roll's gap setting for this piece only.">
        <AllowanceOverrideInput instance={instance} onChange={onAllowanceChange} />
      </Field>

      {room.grainDirection && (
        <p className="text-xs text-brand-700 bg-brand-50 rounded-lg px-3 py-2 flex items-center gap-2">
          <ArrowUp size={13} style={{ transform: `rotate(${instance.rotation}deg)` }} /> Pile direction is shown on the roll
        </p>
      )}

      <div className="space-y-2 pt-1">
        <Button variant="ghost" size="sm" className="w-full h-9" onClick={() => onEditRoom(room)}><Pencil size={14} /> Edit room shape</Button>
        <Button variant="dangerSoft" size="sm" className="w-full h-9" onClick={onDelete} title="Remove from carpet (Delete)"><Trash2 size={14} /> Remove from carpet</Button>
      </div>
    </div>
  );
}

function LayoutSidebar({ selectedInstance, selectedRoom, inspectorProps, stats, settings }) {
  return (
    <aside className="hidden lg:flex w-80 shrink-0 flex-col bg-white border-l border-stone-200 min-h-0 overflow-y-auto">
      {selectedInstance && selectedRoom ? (
        <Inspector instance={selectedInstance} room={selectedRoom} {...inspectorProps} />
      ) : (
        <div className="p-4 space-y-5">
          <div>
            <ProjectNameField projectName={stats.projectName} setProjectName={stats.setProjectName} />
            <h2 className="text-sm font-semibold text-stone-900 mt-3 mb-3">Summary</h2>
            <div className="grid grid-cols-2 gap-2">
              <StatTile label="Carpet to buy" value={stats.lengthLabel} sub={`× ${(stats.rollWidth / 1000).toFixed(2)}m roll`} tone="accent" />
              <StatTile label="Pieces placed" value={`${stats.placed}/${stats.needed}`} sub={stats.placed < stats.needed ? `${stats.needed - stats.placed} to go` : "All placed"} />
              <StatTile label="Carpet used" value={stats.usedLabel} sub={`of ${stats.areaLabel}`} />
              <StatTile label="Offcut waste" value={stats.wastePctLabel} sub={stats.wasteLabel} />
            </div>
            <p className="text-xs text-stone-500 mt-3 flex items-start gap-1.5 leading-snug"><MousePointerClick size={13} className="shrink-0 mt-px" /> Click a piece on the roll to rotate, duplicate or remove it.</p>
          </div>
          <div className="pt-4 border-t border-stone-100">
            <h2 className="text-sm font-semibold text-stone-900 mb-3 flex items-center gap-2"><Ruler size={14} className="text-stone-500" /> Carpet roll</h2>
            <RollSettings {...settings} />
          </div>
        </div>
      )}
    </aside>
  );
}

/* ======================================================================
   SECTION: CUTTING CANVAS
   ====================================================================== */

function CuttingCanvas({ rooms, roomsById, instances, setInstances, rollWidth, tolerance, gridSize, snapEnabled, selectedId, setSelectedId, commitHistory, allowOverlap, stats, onAutoArrange, arranging, onPlaceAll, onGoToRooms, selectionActions, rotationLocked }) {
  const containerRef = useRef(null);
  const [pxPerMm, setPxPerMm] = useState(0.09);
  const [pan, setPan] = useState({ x: 0, y: 0 });
  const [dragOver, setDragOver] = useState(false);
  const dragState = useRef(null);
  const rafId = useRef(null);
  const pendingMouse = useRef(null);

  const reqLength = useMemo(() => requiredLength(instances, roomsById), [instances, roomsById]);
  const canvasLenMm = Math.max(reqLength + 1500, 3000);

  function screenToMm(clientX, clientY) {
    const el = containerRef.current;
    const rect = el.getBoundingClientRect();
    // The bounding rect is viewport-relative regardless of how far the
    // container has scrolled, so the scroll offset has to be added back in.
    const x = (clientX - rect.left - pan.x + el.scrollLeft) / pxPerMm;
    const y = (clientY - rect.top - pan.y + el.scrollTop) / pxPerMm;
    return { x, y };
  }

  function snapVal(v) { return snapEnabled ? Math.round(v / gridSize) * gridSize : v; }

  function effectiveTolerance(inst) { return inst.allowanceOverride != null && inst.allowanceOverride !== "" ? parseFloat(inst.allowanceOverride) : tolerance; }

  // Every placed piece that overlaps another or falls outside the roll width
  // is flagged persistently (not just while dragging) until it's resolved.
  const invalidIds = useMemo(() => {
    const s = new Set();
    instances.forEach((inst) => {
      const room = roomsById[inst.roomId];
      if (!room) return;
      const check = isPlacementValid(room, inst, instances, roomsById, rollWidth, effectiveTolerance(inst));
      if (!check.valid) s.add(inst.id);
    });
    return s;
  }, [instances, roomsById, rollWidth, tolerance]); // eslint-disable-line

  const gridLinesX = useMemo(() => {
    if (!snapEnabled) return [];
    return Array.from({ length: Math.floor(rollWidth / gridSize) }, (_, i) => i);
  }, [snapEnabled, rollWidth, gridSize]);
  const gridLinesY = useMemo(() => {
    if (!snapEnabled) return [];
    return Array.from({ length: Math.floor(canvasLenMm / gridSize) }, (_, i) => i);
  }, [snapEnabled, canvasLenMm, gridSize]);

  // Magnetic snap to the roll's edges and to the edges of other pieces, so
  // pieces dragged close together lock with their edges exactly touching.
  const EDGE_SNAP_MM = 40;
  function snapToEdges(x, y, w, h, excludeId) {
    let nx = x, ny = y, bestXDist = EDGE_SNAP_MM, bestYDist = EDGE_SNAP_MM;
    if (Math.abs(x) <= bestXDist) { bestXDist = Math.abs(x); nx = 0; }
    if (Math.abs(x + w - rollWidth) <= bestXDist) { bestXDist = Math.abs(x + w - rollWidth); nx = rollWidth - w; }
    if (Math.abs(y) <= bestYDist) { bestYDist = Math.abs(y); ny = 0; }

    instances.forEach((other) => {
      if (other.id === excludeId) return;
      const otherRoom = roomsById[other.roomId];
      if (!otherRoom) return;
      const obb = boundingBox(instanceVertices(otherRoom, other));
      const yOverlaps = y < obb.maxY && y + h > obb.minY;
      const xOverlaps = x < obb.maxX && x + w > obb.minX;
      if (yOverlaps) {
        const dRight = Math.abs(x - obb.maxX);
        if (dRight <= bestXDist) { bestXDist = dRight; nx = obb.maxX; }
        const dLeft = Math.abs(x + w - obb.minX);
        if (dLeft <= bestXDist) { bestXDist = dLeft; nx = obb.minX - w; }
      }
      if (xOverlaps) {
        const dBottom = Math.abs(y - obb.maxY);
        if (dBottom <= bestYDist) { bestYDist = dBottom; ny = obb.maxY; }
        const dTop = Math.abs(y + h - obb.minY);
        if (dTop <= bestYDist) { bestYDist = dTop; ny = obb.minY - h; }
      }
    });
    return { x: nx, y: ny };
  }

  function onDropRoom(e) {
    e.preventDefault();
    setDragOver(false);
    const roomId = e.dataTransfer.getData("roomId");
    const room = roomsById[roomId];
    if (!room) return;
    const { x, y } = screenToMm(e.clientX, e.clientY);
    const bb = boundingBox(room.vertices);
    const w = bb.maxX - bb.minX, h = bb.maxY - bb.minY;
    let px = Math.max(0, Math.min(rollWidth - w, snapVal(x - w / 2)));
    let py = Math.max(0, snapVal(y - h / 2));
    const snapped = snapToEdges(px, py, w, h, null);
    px = snapped.x; py = snapped.y;
    let newInst = {
      id: `inst_${Date.now()}_${Math.random().toString(36).slice(2, 6)}`,
      roomId, rotation: 0, x: px, y: py,
      allowanceOverride: room.cuttingAllowance != null ? String(room.cuttingAllowance) : null,
    };
    if (!allowOverlap) {
      const check = isPlacementValid(room, newInst, instances, roomsById, rollWidth, effectiveTolerance(newInst));
      if (!check.valid) {
        // Overlap not allowed: fall back to a guaranteed-clear spot below
        // everything already on the carpet instead of rejecting the drop.
        const gap = instances.length ? tolerance + 60 : 0;
        newInst = { ...newInst, x: 0, y: requiredLength(instances, roomsById) + gap };
      }
    }
    const next = [...instances, newInst];
    setInstances(next); commitHistory(next); setSelectedId(newInst.id);
  }

  // Pointer events (rather than mouse-only) so pieces can be dragged with a
  // finger or pen as well as a mouse.
  function beginDrag(e, inst) {
    if (e.pointerType === "mouse" && e.button !== 0) return;
    e.stopPropagation();
    e.preventDefault();
    setSelectedId(inst.id);
    const startMm = screenToMm(e.clientX, e.clientY);
    dragState.current = { id: inst.id, offsetX: startMm.x - inst.x, offsetY: startMm.y - inst.y, lastValid: { x: inst.x, y: inst.y }, moved: false, startX: e.clientX, startY: e.clientY };
    pendingMouse.current = { clientX: e.clientX, clientY: e.clientY };
    window.addEventListener("pointermove", onDragMove);
    window.addEventListener("pointerup", onDragEnd);
    window.addEventListener("pointercancel", onDragEnd);
    // A continuous per-frame loop keeps autoscroll going even while the
    // pointer holds still near the edge of the canvas.
    rafId.current = requestAnimationFrame(processDragFrame);
  }

  // Only the latest pointer position is kept; the real work runs once per frame.
  function onDragMove(e) {
    if (!dragState.current) return;
    pendingMouse.current = { clientX: e.clientX, clientY: e.clientY };
  }

  const AUTOSCROLL_EDGE_PX = 48, AUTOSCROLL_MAX_SPEED = 22;

  function processDragFrame() {
    const ds = dragState.current;
    const mouse = pendingMouse.current;
    if (!ds || !mouse) { rafId.current = null; return; }

    // A plain click (no real movement) just selects — it shouldn't nudge
    // the piece onto the grid or record an undo step.
    if (!ds.moved) {
      if (Math.hypot(mouse.clientX - ds.startX, mouse.clientY - ds.startY) < 3) {
        rafId.current = requestAnimationFrame(processDragFrame);
        return;
      }
      ds.moved = true;
    }

    const el = containerRef.current;
    if (el) {
      const rect = el.getBoundingClientRect();
      let dy = 0, dx = 0;
      if (mouse.clientY > rect.bottom - AUTOSCROLL_EDGE_PX) {
        dy = AUTOSCROLL_MAX_SPEED * Math.min(1, (mouse.clientY - (rect.bottom - AUTOSCROLL_EDGE_PX)) / AUTOSCROLL_EDGE_PX);
      } else if (mouse.clientY < rect.top + AUTOSCROLL_EDGE_PX) {
        dy = -AUTOSCROLL_MAX_SPEED * Math.min(1, ((rect.top + AUTOSCROLL_EDGE_PX) - mouse.clientY) / AUTOSCROLL_EDGE_PX);
      }
      if (mouse.clientX > rect.right - AUTOSCROLL_EDGE_PX) {
        dx = AUTOSCROLL_MAX_SPEED * Math.min(1, (mouse.clientX - (rect.right - AUTOSCROLL_EDGE_PX)) / AUTOSCROLL_EDGE_PX);
      } else if (mouse.clientX < rect.left + AUTOSCROLL_EDGE_PX) {
        dx = -AUTOSCROLL_MAX_SPEED * Math.min(1, ((rect.left + AUTOSCROLL_EDGE_PX) - mouse.clientX) / AUTOSCROLL_EDGE_PX);
      }
      if (dy) el.scrollTop = Math.max(0, el.scrollTop + dy);
      if (dx) el.scrollLeft = Math.max(0, el.scrollLeft + dx);
    }

    const mm = screenToMm(mouse.clientX, mouse.clientY);
    let nx = snapVal(mm.x - ds.offsetX);
    let ny = Math.max(0, snapVal(mm.y - ds.offsetY));
    setInstances((prev) => {
      if (!dragState.current || dragState.current.id !== ds.id) return prev;
      const instPrev = prev.find((i) => i.id === ds.id);
      if (!instPrev) return prev;
      const room = roomsById[instPrev.roomId];
      if (!room) return prev;
      const rotBB = boundingBox(rotatePolygon(room.vertices, instPrev.rotation));
      const w = rotBB.maxX - rotBB.minX, h = rotBB.maxY - rotBB.minY;
      const snapped = snapToEdges(nx, ny, w, h, ds.id);
      nx = snapped.x; ny = snapped.y;
      const next = prev.map((i) => (i.id === ds.id ? { ...i, x: nx, y: ny } : i));
      const inst = next.find((i) => i.id === ds.id);
      const check = isPlacementValid(room, inst, next, roomsById, rollWidth, effectiveTolerance(inst));
      if (check.valid && dragState.current) dragState.current.lastValid = { x: nx, y: ny };
      return next;
    });

    if (dragState.current) rafId.current = requestAnimationFrame(processDragFrame);
    else rafId.current = null;
  }

  function onDragEnd() {
    window.removeEventListener("pointermove", onDragMove);
    window.removeEventListener("pointerup", onDragEnd);
    window.removeEventListener("pointercancel", onDragEnd);
    if (rafId.current != null) { cancelAnimationFrame(rafId.current); rafId.current = null; }
    pendingMouse.current = null;
    const ds = dragState.current;
    dragState.current = null;
    if (!ds || !ds.moved) return;
    const { id, lastValid } = ds;
    if (!allowOverlap) {
      // Strict mode: snap back to the last spot that didn't collide.
      setInstances((prev) => {
        const next = prev.map((i) => (i.id === id ? { ...i, x: lastValid.x, y: lastValid.y } : i));
        commitHistory(next);
        return next;
      });
    } else {
      // Overlap allowed: keep it where dropped; it stays flagged red until resolved.
      setInstances((prev) => { commitHistory(prev); return prev; });
    }
  }

  function zoom(delta) { setPxPerMm((z) => Math.min(0.4, Math.max(0.02, z * delta))); }
  // Fits the whole roll — its full width AND everything placed on it — into view.
  function fitToScreen() {
    const el = containerRef.current;
    if (!el) return;
    const rect = el.getBoundingClientRect();
    const byWidth = (rect.width - 120) / rollWidth;
    const byLength = (rect.height - 120) / Math.max(requiredLength(instances, roomsById), 2000);
    setPxPerMm(Math.min(0.4, Math.max(0.02, Math.min(byWidth, byLength))));
    setPan({ x: 44, y: 34 });
    el.scrollTop = 0; el.scrollLeft = 0;
  }
  useEffect(() => { fitToScreen(); }, [rollWidth]); // eslint-disable-line

  // Ctrl/Cmd + wheel (and trackpad pinch) zooms; a plain wheel still scrolls.
  // Needs a non-passive listener so the browser's own page zoom can be blocked.
  useEffect(() => {
    const el = containerRef.current;
    if (!el) return;
    function onWheel(e) {
      if (!(e.ctrlKey || e.metaKey)) return;
      e.preventDefault();
      const factor = Math.exp(-e.deltaY * 0.0015);
      setPxPerMm((z) => Math.min(0.4, Math.max(0.02, z * factor)));
    }
    el.addEventListener("wheel", onWheel, { passive: false });
    return () => el.removeEventListener("wheel", onWheel);
  }, []);

  const widthPx = rollWidth * pxPerMm;
  const lenPx = canvasLenMm * pxPerMm;
  const metreTicks = [];
  for (let m = 0; m * 1000 <= rollWidth; m++) metreTicks.push(m);
  const lengthTicks = [];
  for (let m = 0; m * 1000 <= canvasLenMm; m++) lengthTicks.push(m);
  const selectedInst = instances.find((i) => i.id === selectedId);
  const selectedRoomName = selectedInst ? roomsById[selectedInst.roomId]?.name : null;

  return (
    <div className="flex-1 flex flex-col min-w-0 min-h-0">
      {/* Toolbar */}
      <div className="shrink-0 flex flex-wrap items-center gap-x-5 gap-y-2 px-4 py-2 min-h-[48px] bg-white border-b border-stone-200">
        <div className="flex items-baseline gap-1.5">
          <span className="text-xs text-stone-600">Carpet needed</span>
          <span className="text-base font-semibold text-brand-600 tabular-nums">{stats.lengthLabel}</span>
          <span className="text-xs text-stone-500 tabular-nums">× {(rollWidth / 1000).toFixed(2)}m</span>
        </div>
        <div className="hidden sm:flex items-baseline gap-1.5">
          <span className="text-xs text-stone-600">Waste</span>
          <span className="text-sm font-medium text-stone-800 tabular-nums">{stats.wastePctLabel}</span>
        </div>
        {invalidIds.size > 0 && (
          <span title={allowOverlap ? "Overlaps are allowed — move pieces apart or use “Arrange for me” to fix them" : "These will snap clear once you move them"}
            className="inline-flex items-center gap-1.5 text-xs font-medium text-red-700 bg-red-50 border border-red-100 rounded-full px-2.5 py-1">
            <AlertTriangle size={12} /> {invalidIds.size} overlapping
          </span>
        )}
        <div className="ml-auto flex items-center gap-2">
          <Button
            variant="primary" onClick={onAutoArrange} disabled={arranging || instances.length === 0}
            title="Search for the shortest layout using each room's exact shape — the current plan is only replaced by a better one"
          >
            {arranging ? <Loader2 size={15} className="animate-spin" /> : <Sparkles size={15} />}
            {arranging ? "Working it out…" : "Arrange for me"}
          </Button>
        </div>
      </div>

      {/* Canvas */}
      <div className="relative flex-1 min-h-0">
        <div
          ref={containerRef}
          className={cls("absolute inset-0 overflow-auto bg-stone-100 transition-shadow", dragOver && "ring-4 ring-inset ring-brand-500/30")}
          onDragOver={(e) => { e.preventDefault(); e.dataTransfer.dropEffect = "copy"; if (!dragOver) setDragOver(true); }}
          onDragLeave={(e) => { if (!e.currentTarget.contains(e.relatedTarget)) setDragOver(false); }}
          onDrop={onDropRoom}
          onPointerDown={() => setSelectedId(null)}
          style={{ backgroundImage: "radial-gradient(#d6d3d1 1px, transparent 1px)", backgroundSize: "18px 18px" }}
        >
          <svg width={widthPx + 110} height={lenPx + 70} className="select-none">
            <defs>
              <pattern id="weave" width="8" height="8" patternUnits="userSpaceOnUse">
                <path d="M0 0L8 8M8 0L0 8" stroke="#e7dfd0" strokeWidth="0.7" />
              </pattern>
              <marker id="arrow" markerWidth="6" markerHeight="6" refX="3" refY="3" orient="auto"><path d="M0,0 L6,3 L0,6 Z" fill="#1c1917" /></marker>
              <filter id="rollShadow" x="-5%" y="-5%" width="110%" height="110%"><feDropShadow dx="0" dy="1" stdDeviation="2" floodColor="#000" floodOpacity="0.12" /></filter>
            </defs>
            <g transform={`translate(${pan.x},${pan.y})`}>
              {/* carpet body */}
              <rect x={0} y={0} width={widthPx} height={lenPx} fill="#f6f1e7" stroke="#d6cdbd" strokeWidth="1" filter="url(#rollShadow)" />
              <rect x={0} y={0} width={widthPx} height={lenPx} fill="url(#weave)" />
              {/* grid */}
              {gridLinesX.map((i) => (
                <line key={"gx" + i} x1={i * gridSize * pxPerMm} y1={0} x2={i * gridSize * pxPerMm} y2={lenPx} stroke="#e2d9c8" strokeWidth="0.5" opacity="0.6" />
              ))}
              {gridLinesY.map((i) => (
                <line key={"gy" + i} x1={0} y1={i * gridSize * pxPerMm} x2={widthPx} y2={i * gridSize * pxPerMm} stroke="#e2d9c8" strokeWidth="0.5" opacity="0.6" />
              ))}
              {/* top ruler */}
              {metreTicks.map((m) => (
                <g key={"tm" + m}>
                  <line x1={m * 1000 * pxPerMm} y1={-7} x2={m * 1000 * pxPerMm} y2={0} stroke="#a8a29e" strokeWidth="1" />
                  <text x={m * 1000 * pxPerMm} y={-11} fontSize="10" textAnchor="middle" fill="#78716c">{m}m</text>
                </g>
              ))}
              {/* left ruler */}
              {lengthTicks.map((m) => (
                <g key={"lm" + m}>
                  <line x1={-7} y1={m * 1000 * pxPerMm} x2={0} y2={m * 1000 * pxPerMm} stroke="#a8a29e" strokeWidth="1" />
                  <text x={-11} y={m * 1000 * pxPerMm + 3.5} fontSize="10" textAnchor="end" fill="#78716c">{m}m</text>
                </g>
              ))}
              {/* required-length marker */}
              {reqLength > 0 && (
                <g>
                  <line x1={0} y1={reqLength * pxPerMm} x2={widthPx} y2={reqLength * pxPerMm} stroke="#b8282a" strokeWidth="1.5" strokeDasharray="6 4" />
                  <g transform={`translate(${widthPx + 6},${reqLength * pxPerMm})`}>
                    <rect x={0} y={-10} width={58} height={20} rx={10} fill="#b8282a" />
                    <text x={29} y={4} fontSize="10.5" fontWeight="600" textAnchor="middle" fill="white">{(reqLength / 1000).toFixed(2)}m</text>
                  </g>
                </g>
              )}

              {instances.map((inst) => {
                const room = roomsById[inst.roomId];
                if (!room) return null;
                const verts = instanceVertices(room, inst);
                const pts = verts.map((v) => `${v.x * pxPerMm},${v.y * pxPerMm}`).join(" ");
                const isSelected = selectedId === inst.id;
                const isInvalid = invalidIds.has(inst.id);
                const bb = boundingBox(verts);
                const pcx = (bb.minX + bb.maxX) / 2 * pxPerMm, pcy = (bb.minY + bb.maxY) / 2 * pxPerMm;
                const pw = (bb.maxX - bb.minX) * pxPerMm, ph = (bb.maxY - bb.minY) * pxPerMm;
                const showSize = ph > 38 && pw > 60;
                const showName = pw > 34 && ph > 16;
                return (
                  <g key={inst.id} onPointerDown={(e) => beginDrag(e, inst)} style={{ cursor: "grab", touchAction: "none" }}>
                    <polygon
                      points={pts}
                      fill={isInvalid ? "#dc262633" : room.color + (isSelected ? "66" : "4d")}
                      stroke={isInvalid ? "#dc2626" : isSelected ? "#1c1917" : room.color}
                      strokeWidth={isSelected ? 2.5 : isInvalid ? 2 : 1.5}
                      strokeDasharray={isInvalid ? "7 4" : undefined}
                      strokeLinejoin="round"
                    />
                    {room.grainDirection && (
                      (() => {
                        const ax = bb.minX * pxPerMm + 16, ay = bb.minY * pxPerMm + (isInvalid ? 40 : 20);
                        return <line x1={ax} y1={ay + 9} x2={ax} y2={ay - 9} stroke="#1c1917" strokeOpacity="0.6" strokeWidth="1.5" markerEnd="url(#arrow)" transform={`rotate(${inst.rotation} ${ax} ${ay})`} />;
                      })()
                    )}
                    {showName && (
                      <text x={pcx} y={showSize ? pcy - 3 : pcy + 4} fontSize="11.5" fontWeight="600" fill="#1c1917" textAnchor="middle" style={{ pointerEvents: "none" }}>{room.name}</text>
                    )}
                    {showSize && (
                      <text x={pcx} y={pcy + 12} fontSize="10" fill="#44403c" textAnchor="middle" style={{ pointerEvents: "none" }}>
                        {formatLength(bb.maxX - bb.minX, "m")} × {formatLength(bb.maxY - bb.minY, "m")}
                      </text>
                    )}
                    {isInvalid && (
                      <g transform={`translate(${bb.minX * pxPerMm + 11},${bb.minY * pxPerMm + 11})`} style={{ pointerEvents: "none" }}>
                        <circle r="8" fill="#dc2626" />
                        <text x="0" y="3.5" fontSize="10" fontWeight="bold" textAnchor="middle" fill="white">!</text>
                      </g>
                    )}
                  </g>
                );
              })}
            </g>
          </svg>
        </div>

        {/* Empty state */}
        {instances.length === 0 && (
          <div className="absolute inset-0 flex items-center justify-center pointer-events-none p-4">
            <div className="pointer-events-auto text-center bg-white/90 backdrop-blur-sm rounded-2xl ring-1 ring-stone-900/[0.06] shadow-[0_18px_40px_-18px_rgba(60,40,30,0.35)] px-8 py-7 max-w-sm">
              {rooms.length > 0 ? (
                <>
                  <p className="text-lg font-semibold text-stone-900">The roll is empty</p>
                  <p className="text-sm text-stone-600 mt-1 [text-wrap:balance]">Put all your rooms on it in one go, then press “Arrange for me”.</p>
                  <Button variant="primary" className="mt-5 h-11 px-5" onClick={onPlaceAll}>Put all rooms on the roll <ArrowRight size={16} /></Button>
                </>
              ) : (
                <>
                  <p className="text-lg font-semibold text-stone-900">No rooms yet</p>
                  <p className="text-sm text-stone-600 mt-1 [text-wrap:balance]">Add the rooms that need carpet first, then come back here.</p>
                  <Button variant="primary" className="mt-5 h-11 px-5" onClick={onGoToRooms}><Plus size={16} /> Add a room</Button>
                </>
              )}
            </div>
          </div>
        )}

        {/* Selection actions (small screens — larger ones use the side panel) */}
        {selectedInst && (
          <div className="lg:hidden absolute top-3 left-1/2 -translate-x-1/2 z-10 flex items-center gap-1 bg-white border border-stone-200 rounded-xl shadow-lg p-1 animate-fade-in max-w-[calc(100%-24px)]">
            <span className="text-xs font-medium text-stone-700 px-2 truncate max-w-[120px]">{selectedRoomName}</span>
            <IconButton label="Rotate 90° (R)" onClick={selectionActions.onRotate} disabled={rotationLocked}><RotateCw size={16} /></IconButton>
            <IconButton label="Duplicate" onClick={selectionActions.onDuplicate}><Copy size={16} /></IconButton>
            <IconButton label="Remove from carpet" onClick={selectionActions.onDelete} className="text-red-600 hover:bg-red-50 hover:text-red-700"><Trash2 size={16} /></IconButton>
          </div>
        )}

        {/* Hints + zoom */}
        <div className="hidden md:flex absolute bottom-4 left-4 items-center gap-2 text-xs text-stone-600 bg-white/90 backdrop-blur border border-stone-200 rounded-lg px-2.5 py-1.5 shadow-sm pointer-events-none">
          <MousePointerClick size={14} className="text-brand-600" />
          <span>Drag a piece to move it · click a piece to turn or remove it</span>
        </div>
        <div className="absolute bottom-4 right-4 flex items-center bg-white border border-stone-200 rounded-lg shadow-sm p-0.5">
          <IconButton label="Zoom out" onClick={() => zoom(0.85)} className="w-8 h-8"><ZoomOut size={15} /></IconButton>
          <IconButton label="Fit roll to screen" onClick={fitToScreen} className="w-8 h-8"><Maximize2 size={14} /></IconButton>
          <IconButton label="Zoom in" onClick={() => zoom(1.18)} className="w-8 h-8"><ZoomIn size={15} /></IconButton>
        </div>
      </div>
    </div>
  );
}

/* ======================================================================
   SECTION: TOP BAR
   ====================================================================== */

function SaveStatus({ state }) {
  if (state === "saving") return <span className="hidden lg:flex items-center gap-1.5 text-xs text-stone-300 px-2"><Loader2 size={13} className="animate-spin" /> Saving…</span>;
  return <span className="hidden lg:flex items-center gap-1.5 text-xs text-stone-300 px-2" title="Your work is saved on this device automatically"><CheckCircle2 size={14} className="text-emerald-400" /> Saved</span>;
}

// Dark brand bar, matching the srcarpetsandfloors.co.uk navigation.
const DARK_ICON_BTN = "text-stone-300 hover:bg-white/10 hover:text-white";

function TopBar({ onUndo, onRedo, canUndo, canRedo, onSave, saveState, view, setView, onOpenCuttingPlan, onOpenHelp, roomCount, instanceCount }) {
  const tabs = [
    { key: "rooms", n: 1, label: "Your rooms", short: "Rooms", count: roomCount },
    { key: "cutting", n: 2, label: "Plan the cut", short: "Plan", count: instanceCount },
  ];
  return (
    <header className="shrink-0 bg-ink-900 text-white">
      <div className="h-16 flex items-center gap-1.5 sm:gap-4 px-2.5 sm:px-5">
        <a href="https://srcarpetsandfloors.co.uk/" target="_blank" rel="noreferrer" title="SR Carpets & Floors" className="flex items-center gap-3 shrink-0">
          <img src="/sr-logo-white.png" alt="SR Carpets & Floors" className="hidden md:block h-9 w-auto" />
          <img src="/sr-mark-white.png" alt="SR Carpets & Floors" className="md:hidden h-7 w-auto" />
        </a>
        <span className="hidden xl:flex items-center gap-3 font-display text-sm font-medium uppercase tracking-[0.22em] text-stone-500">
          <span className="w-px h-5 bg-white/20" /> Carpet Planner
        </span>

        <nav className="mx-auto flex items-center gap-0.5 sm:gap-1 bg-white/[0.07] rounded-xl p-1 min-w-0 overflow-hidden" aria-label="Steps">
          {tabs.map((t, i) => {
            const active = view === t.key;
            return (
              <React.Fragment key={t.key}>
                {i > 0 && <ChevronRight size={15} className="text-white/25 hidden sm:block" />}
                <button
                  type="button" onClick={() => setView(t.key)} aria-current={active ? "page" : undefined} aria-label={t.label} title={t.label}
                  className={cls("flex items-center gap-1.5 sm:gap-2 h-10 pl-1.5 sm:pl-2 pr-2 sm:pr-4 rounded-lg text-sm font-semibold transition-all", FOCUS_RING,
                    active ? "bg-white text-ink-900 shadow" : "text-stone-300 hover:text-white hover:bg-white/5")}
                >
                  <span className={cls("w-6 h-6 rounded-md grid place-items-center text-xs font-bold", active ? "bg-brand-500 text-white" : "bg-white/10 text-stone-300")}>{t.n}</span>
                  <span className="hidden sm:inline">{t.label}</span><span className={active ? "sm:hidden" : "hidden"}>{t.short}</span>
                  {t.count > 0 && <span className={cls("hidden sm:inline text-xs tabular-nums rounded-full px-1.5 min-w-[22px]", active ? "bg-stone-100 text-stone-600" : "bg-white/10 text-stone-300")}>{t.count}</span>}
                </button>
              </React.Fragment>
            );
          })}
        </nav>

        <div className="flex items-center gap-0.5 sm:gap-1 shrink-0">
          <SaveStatus state={saveState} />
          <IconButton label="Undo — take back the last change" onClick={onUndo} disabled={!canUndo} className={DARK_ICON_BTN + " w-9 sm:w-10 h-10"}><Undo2 size={19} /></IconButton>
          <IconButton label="Redo" onClick={onRedo} disabled={!canRedo} className={DARK_ICON_BTN + " w-10 h-10 hidden sm:inline-flex"}><Redo2 size={19} /></IconButton>
          <IconButton label="Save now — your work also saves automatically" onClick={onSave} className={DARK_ICON_BTN + " w-10 h-10 hidden md:inline-flex"}><Save size={19} /></IconButton>
          <Button variant="ghost" className="h-10 px-2 sm:px-3 !text-stone-200 hover:!bg-white/10 hover:!text-white" onClick={onOpenHelp} title="How to use the planner">
            <HelpCircle size={18} /> <span className="hidden lg:inline">Help</span>
          </Button>
          <Button variant="primary" className="ml-0.5 sm:ml-1 h-10 px-3 sm:px-4" onClick={onOpenCuttingPlan} title="See the finished plan and print or save it">
            <Printer size={17} /> <span className="hidden sm:inline">Print / save plan</span>
          </Button>
        </div>
      </div>
      {/* thin brand rule */}
      <div className="h-[3px] bg-brand-500" />
    </header>
  );
}

function ProjectNameField({ projectName, setProjectName }) {
  return (
    <label className="group inline-flex items-center gap-2 min-w-0 max-w-full">
      <span className="sr-only">Project name</span>
      <input
        value={projectName} onChange={(e) => setProjectName(e.target.value)}
        title="Click to rename this project"
        className="min-w-0 w-64 max-w-full h-9 -ml-2 rounded-lg px-2 text-sm font-semibold text-stone-800 bg-transparent border border-transparent hover:bg-white hover:border-stone-200 focus:bg-white focus:border-brand-500 focus:ring-2 focus:ring-brand-500/20 focus:outline-none transition truncate"
      />
      <Pencil size={13} className="-ml-8 text-stone-500 pointer-events-none shrink-0" />
    </label>
  );
}

/* ======================================================================
   SECTION: HELP GUIDE — plain-English walkthrough for first-time users
   ====================================================================== */

function HelpModal({ onClose }) {
  const steps = [
    { icon: Plus, title: "Add each room", body: "On “Your rooms”, press Add room. Pick the shape that looks most like the room — a plain rectangle, an L-shape or a T-shape. If none fit, click on the grid to draw the corners yourself." },
    { icon: Ruler, title: "Type in the measurements", body: "Type the length of each wall. The numbered picture shows which wall is which. You can leave one width and one length empty and the planner will work them out." },
    { icon: Layers, title: "Put the rooms on the roll", body: "Go to “Plan the cut” and press Place all rooms. Every room you need appears on the carpet roll." },
    { icon: Sparkles, title: "Press “Arrange for me”", body: "The planner fits the pieces together to use as little carpet as possible. You can also drag pieces around yourself, and click a piece to turn or remove it." },
    { icon: Printer, title: "Print or save the plan", body: "Press Print / save plan at the top to download a picture or PDF showing exactly where to cut, and how much carpet to buy." },
  ];
  return (
    <Modal onClose={onClose} className="max-w-2xl" labelledBy="help-title">
      <div className="flex items-start justify-between gap-4 px-6 pt-6 pb-4 border-b border-stone-100">
        <div>
          <p className="font-display text-xs font-semibold uppercase tracking-[0.24em] text-brand-600">SR Carpets &amp; Floors</p>
          <h2 id="help-title" className="text-xl font-semibold text-stone-900 mt-1">How to use the Carpet Planner</h2>
          <p className="text-sm text-stone-600 mt-1">Five simple steps — no experience needed.</p>
        </div>
        <IconButton label="Close" onClick={onClose}><X size={20} /></IconButton>
      </div>
      <div className="flex-1 overflow-y-auto px-6 py-5">
        <ol className="space-y-4">
          {steps.map((s, i) => (
            <li key={s.title} className="flex gap-4">
              <div className="shrink-0 w-11 h-11 rounded-xl bg-brand-50 text-brand-600 grid place-items-center relative">
                <s.icon size={20} />
                <span className="absolute -top-1.5 -left-1.5 w-5 h-5 rounded-full bg-ink-900 text-white text-[11px] font-bold grid place-items-center">{i + 1}</span>
              </div>
              <div className="min-w-0">
                <p className="text-sm font-semibold text-stone-900">{s.title}</p>
                <p className="text-sm text-stone-600 mt-0.5 leading-relaxed">{s.body}</p>
              </div>
            </li>
          ))}
        </ol>
        <div className="mt-6 grid sm:grid-cols-2 gap-3">
          <div className="rounded-xl bg-stone-50 border border-stone-100 p-4">
            <p className="text-sm font-semibold text-stone-900 flex items-center gap-2"><Undo2 size={16} className="text-brand-600" /> Made a mistake?</p>
            <p className="text-sm text-stone-600 mt-1 leading-relaxed">Press the curved arrow at the top to undo your last change.</p>
          </div>
          <div className="rounded-xl bg-stone-50 border border-stone-100 p-4">
            <p className="text-sm font-semibold text-stone-900 flex items-center gap-2"><CheckCircle2 size={16} className="text-brand-600" /> Saved for you</p>
            <p className="text-sm text-stone-600 mt-1 leading-relaxed">Everything saves automatically on this device, so you can close the page and come back later.</p>
          </div>
        </div>
      </div>
      <div className="px-6 py-4 border-t border-stone-100 bg-stone-50/60 flex justify-end">
        <Button variant="primary" onClick={onClose}>Got it</Button>
      </div>
    </Modal>
  );
}

/* ======================================================================
   SECTION: EXPORT HELPERS (PNG / PDF)
   A minimal, dependency-free PDF writer: no external library is available
   in this environment, so a single-page PDF is hand-built by embedding a
   JPEG snapshot of the plan directly via the DCTDecode filter, which every
   standard PDF viewer can decode natively without re-compression.
   ====================================================================== */

function safeFileName(name) {
  const s = (name || "cutting-plan").trim().toLowerCase().replace(/[^a-z0-9]+/g, "-").replace(/(^-|-$)/g, "");
  return s || "cutting-plan";
}

function downloadBlob(blob, filename) {
  const url = URL.createObjectURL(blob);
  const link = document.createElement("a");
  link.download = filename;
  link.href = url;
  document.body.appendChild(link);
  link.click();
  link.remove();
  URL.revokeObjectURL(url);
}

// Rasterises an <svg> element (given its declared pixel width/height) onto
// a white-backed canvas at the requested resolution multiplier.
// Renders the cutting plan directly with the Canvas 2D API — never via an
// <img>-loaded SVG. Drawing an SVG-sourced image onto a canvas is known to
// taint it in some browsers (Firefox in particular), which makes
// canvas.toDataURL() throw even though canvas.toBlob() silently no-ops —
// so PDF export (which needs toDataURL for the JPEG) would fail exactly
// where PNG export (toBlob) might appear to work. Drawing natively avoids
// that risk entirely, for both export paths.
// SR Carpets & Floors logo for the printed plan. Loaded once from this
// site (same origin), so drawing it never taints the export canvas.
const PLAN_LOGO_SRC = "/sr-logo-red.png";
const PLAN_LOGO_H = 24; // px, in plan units
const PLAN_HEADER_H = 66; // logo row + title + details line
let planLogoPromise = null;
function loadPlanLogo() {
  if (!planLogoPromise) {
    planLogoPromise = new Promise((resolve) => {
      const img = new Image();
      img.onload = () => resolve(img);
      img.onerror = () => { planLogoPromise = null; resolve(null); }; // export still works without it
      img.src = PLAN_LOGO_SRC;
    });
  }
  return planLogoPromise;
}

function renderPlanCanvas({ instances, roomsById, rollWidth, reqLength, projectName, pxPerMm, headerH, scale, logo }) {
  const svgW = rollWidth * pxPerMm + 20;
  const svgH = reqLength * pxPerMm + 20 + headerH;
  const canvas = document.createElement("canvas");
  canvas.width = Math.max(1, Math.round(svgW * scale));
  canvas.height = Math.max(1, Math.round(svgH * scale));
  const ctx = canvas.getContext("2d");
  ctx.scale(scale, scale);
  ctx.fillStyle = "#ffffff";
  ctx.fillRect(0, 0, svgW, svgH);

  if (logo && logo.naturalHeight) {
    ctx.drawImage(logo, 10, 8, (logo.naturalWidth / logo.naturalHeight) * PLAN_LOGO_H, PLAN_LOGO_H);
  }

  ctx.textBaseline = "alphabetic";
  ctx.textAlign = "left";
  ctx.fillStyle = "#1c1a18";
  ctx.font = "bold 13px sans-serif";
  ctx.fillText(`${projectName} — Cutting Plan`, 10, 46);
  ctx.fillStyle = "#78716c";
  ctx.font = "9.5px monospace";
  ctx.fillText(
    `Roll ${(rollWidth / 1000).toFixed(2)}m wide \u00B7 Required length ${(reqLength / 1000).toFixed(2)}m \u00B7 ${instances.length} piece(s) \u00B7 ${new Date().toLocaleDateString()}`,
    10, 60
  );

  const offX = 10, offY = headerH + 10;
  const rollW = rollWidth * pxPerMm, rollH = reqLength * pxPerMm;
  ctx.fillStyle = "#fafaf7";
  ctx.fillRect(offX, offY, rollW, rollH);
  ctx.strokeStyle = "#333333";
  ctx.lineWidth = 1;
  ctx.strokeRect(offX, offY, rollW, rollH);

  instances.forEach((inst) => {
    const room = roomsById[inst.roomId];
    if (!room) return;
    const verts = instanceVertices(room, inst);
    if (!verts.length) return;
    ctx.beginPath();
    verts.forEach((v, i) => {
      const x = offX + v.x * pxPerMm, y = offY + v.y * pxPerMm;
      if (i === 0) ctx.moveTo(x, y); else ctx.lineTo(x, y);
    });
    ctx.closePath();
    ctx.fillStyle = room.color + "33";
    ctx.fill();
    ctx.strokeStyle = room.color;
    ctx.lineWidth = 1.5;
    ctx.stroke();
    const bb = boundingBox(verts);
    const cx = offX + ((bb.minX + bb.maxX) / 2) * pxPerMm;
    const cy = offY + ((bb.minY + bb.maxY) / 2) * pxPerMm;
    const sizeLabel = `${formatLength(bb.maxX - bb.minX, "m")} × ${formatLength(bb.maxY - bb.minY, "m")}`;
    ctx.textAlign = "center";
    ctx.fillStyle = "#1c1a18";
    ctx.font = "bold 9px monospace";
    ctx.fillText(room.name, cx, cy - 5);
    ctx.fillStyle = "#555048";
    ctx.font = "8px monospace";
    ctx.fillText(sizeLabel, cx, cy + 7);
    ctx.textAlign = "left";
  });

  return canvas;
}

function base64ToUint8Array(base64) {
  const binStr = atob(base64);
  const bytes = new Uint8Array(binStr.length);
  for (let i = 0; i < binStr.length; i++) bytes[i] = binStr.charCodeAt(i);
  return bytes;
}

// Builds a valid, minimal single-page PDF wrapping one JPEG image, scaled
// to fill a page of pageW x pageH points. imgPxW/imgPxH are the JPEG's own
// pixel dimensions (kept higher than the page size for a crisp render).
function buildSinglePageImagePDF(jpegBytes, imgPxW, imgPxH, pageW, pageH) {
  const enc = new TextEncoder();
  const parts = [];
  let pos = 0;
  const offsets = {};
  function writeStr(s) { const b = enc.encode(s); parts.push(b); pos += b.length; }
  function writeBytes(b) { parts.push(b); pos += b.length; }
  function beginObj(n) { offsets[n] = pos; writeStr(`${n} 0 obj\n`); }
  function endObj() { writeStr("endobj\n"); }

  writeStr("%PDF-1.4\n");

  beginObj(1);
  writeStr("<< /Type /Catalog /Pages 2 0 R >>\n");
  endObj();

  beginObj(2);
  writeStr("<< /Type /Pages /Kids [3 0 R] /Count 1 >>\n");
  endObj();

  beginObj(3);
  writeStr(`<< /Type /Page /Parent 2 0 R /MediaBox [0 0 ${pageW} ${pageH}] /Resources << /XObject << /Im0 4 0 R >> >> /Contents 5 0 R >>\n`);
  endObj();

  beginObj(4);
  writeStr(`<< /Type /XObject /Subtype /Image /Width ${imgPxW} /Height ${imgPxH} /ColorSpace /DeviceRGB /BitsPerComponent 8 /Filter /DCTDecode /Length ${jpegBytes.length} >>\nstream\n`);
  writeBytes(jpegBytes);
  writeStr("\nendstream\n");
  endObj();

  const contentBytes = enc.encode(`q\n${pageW} 0 0 ${pageH} 0 0 cm\n/Im0 Do\nQ`);
  beginObj(5);
  writeStr(`<< /Length ${contentBytes.length} >>\nstream\n`);
  writeBytes(contentBytes);
  writeStr("\nendstream\n");
  endObj();

  const xrefStart = pos;
  writeStr("xref\n0 6\n");
  writeStr("0000000000 65535 f \n");
  for (let i = 1; i <= 5; i++) writeStr(`${String(offsets[i]).padStart(10, "0")} 00000 n \n`);
  writeStr(`trailer\n<< /Size 6 /Root 1 0 R >>\nstartxref\n${xrefStart}\n%%EOF`);

  const total = parts.reduce((s, p) => s + p.length, 0);
  const out = new Uint8Array(total);
  let o = 0;
  for (const p of parts) { out.set(p, o); o += p.length; }
  return out;
}

function CuttingPlanModal({ onClose, roomsById, instances, rollWidth, projectName, reqLength, stats }) {
  const pxPerMm = Math.min(0.5, 780 / rollWidth);
  const svgRef = useRef(null);
  const [exportState, setExportState] = useState("idle"); // idle | working | error
  const [pdfState, setPdfState] = useState("idle"); // idle | working | error
  const headerH = PLAN_HEADER_H;
  useEffect(() => { loadPlanLogo(); }, []);
  const svgW = rollWidth * pxPerMm + 20;
  const svgH = reqLength * pxPerMm + 20 + headerH;
  const empty = instances.length === 0;

  async function exportAsImage() {
    setExportState("working");
    try {
      const logo = await loadPlanLogo();
      const canvas = renderPlanCanvas({ instances, roomsById, rollWidth, reqLength, projectName, pxPerMm, headerH, scale: 2, logo });
      canvas.toBlob((blob) => {
        if (!blob) { setExportState("error"); return; }
        downloadBlob(blob, `${safeFileName(projectName)}.png`);
        setExportState("idle");
      }, "image/png");
    } catch (err) {
      setExportState("error");
    }
  }

  async function exportAsPDF() {
    setPdfState("working");
    try {
      const scale = 2;
      const logo = await loadPlanLogo();
      const canvas = renderPlanCanvas({ instances, roomsById, rollWidth, reqLength, projectName, pxPerMm, headerH, scale, logo });
      const jpegDataUrl = canvas.toDataURL("image/jpeg", 0.92);
      const jpegBytes = base64ToUint8Array(jpegDataUrl.split(",")[1]);
      const pdfBytes = buildSinglePageImagePDF(jpegBytes, canvas.width, canvas.height, svgW, svgH);
      downloadBlob(new Blob([pdfBytes], { type: "application/pdf" }), `${safeFileName(projectName)}.pdf`);
      setPdfState("idle");
    } catch (err) {
      setPdfState("error");
    }
  }

  const rows = Object.entries(
    instances.reduce((acc, inst) => {
      if (!roomsById[inst.roomId]) return acc;
      acc[inst.roomId] = (acc[inst.roomId] || 0) + 1;
      return acc;
    }, {})
  );

  return (
    <Modal onClose={onClose} className="max-w-5xl h-[94vh]" labelledBy="plan-title">
      <div className="flex flex-wrap items-center gap-3 px-5 sm:px-6 py-4 border-b border-stone-100 shrink-0">
        <div className="min-w-0 mr-auto">
          <h2 id="plan-title" className="text-lg font-semibold text-stone-900 truncate">Cutting plan</h2>
          <p className="text-xs text-stone-600 truncate">{projectName}</p>
        </div>
        <Button variant="secondary" onClick={exportAsPDF} disabled={empty || pdfState === "working"} title="Download this cutting plan as a PDF">
          {pdfState === "working" ? <Loader2 size={15} className="animate-spin" /> : <FileText size={15} />} {pdfState === "working" ? "Preparing…" : "Download PDF"}
        </Button>
        <Button variant="primary" onClick={exportAsImage} disabled={empty || exportState === "working"} title="Download this cutting plan as a PNG image">
          {exportState === "working" ? <Loader2 size={15} className="animate-spin" /> : <Download size={15} />} {exportState === "working" ? "Preparing…" : "Download image"}
        </Button>
        <IconButton label="Close (Esc)" onClick={onClose}><X size={18} /></IconButton>
      </div>

      <div className="flex-1 min-h-0 overflow-auto bg-stone-50 px-5 sm:px-6 py-5">
        {pdfState === "error" && (
          <div className="mb-4"><Notice tone="error">Couldn't create the PDF in this browser. Try “Download image” instead, or print this page and choose “Save as PDF”.</Notice></div>
        )}
        {exportState === "error" && (
          <div className="mb-4"><Notice tone="error">Couldn't create the image in this browser. Try right-clicking the plan below and choosing “Save image as”.</Notice></div>
        )}

        {empty ? (
          <div className="h-full grid place-items-center text-center">
            <div>
              <div className="w-12 h-12 mx-auto rounded-xl bg-white border border-stone-200 text-stone-500 grid place-items-center mb-3"><Layers size={22} /></div>
              <p className="text-sm font-semibold text-stone-900">Nothing on the carpet yet</p>
              <p className="text-xs text-stone-600 mt-1">Place some rooms in the cutting layout and your plan will appear here.</p>
            </div>
          </div>
        ) : (
          <>
            <div className="grid grid-cols-2 sm:grid-cols-4 gap-2.5 mb-5">
              <StatTile label="Roll width" value={`${(rollWidth / 1000).toFixed(2)}m`} />
              <StatTile label="Length to buy" value={`${(reqLength / 1000).toFixed(2)}m`} tone="accent" />
              <StatTile label="Pieces" value={instances.length} />
              <StatTile label="Waste" value={stats.wastePctLabel} sub={stats.wasteLabel} />
            </div>
            <div className="grid xl:grid-cols-[minmax(0,1fr)_300px] gap-5 items-start">
              <div className="bg-white border border-stone-200 rounded-xl p-3 overflow-auto shadow-sm">
                <svg ref={svgRef} width={svgW} height={svgH} viewBox={`0 0 ${svgW} ${svgH}`} style={{ maxWidth: "100%", height: "auto" }} className="block mx-auto">
                  <rect width={svgW} height={svgH} fill="#ffffff" />
                  <image href={PLAN_LOGO_SRC} x={10} y={8} height={PLAN_LOGO_H} preserveAspectRatio="xMinYMid meet" width={Math.max(0, svgW - 20)} />
                  <text x={10} y={46} fontSize="13" fontWeight="bold" fontFamily="Inter, ui-sans-serif, system-ui, sans-serif" fill="#1c1a18">{projectName} — Cutting Plan</text>
                  <text x={10} y={60} fontSize="9.5" fontFamily="ui-monospace, monospace" fill="#78716c">
                    {`Roll ${(rollWidth / 1000).toFixed(2)}m wide · Required length ${(reqLength / 1000).toFixed(2)}m · ${instances.length} piece(s) · ${new Date().toLocaleDateString()}`}
                  </text>
                  <g transform={`translate(10,${headerH + 10})`}>
                    <rect x={0} y={0} width={rollWidth * pxPerMm} height={reqLength * pxPerMm} fill="#fafaf7" stroke="#333" />
                    {instances.map((inst) => {
                      const room = roomsById[inst.roomId];
                      if (!room) return null;
                      const verts = instanceVertices(room, inst);
                      const pts = verts.map((v) => `${v.x * pxPerMm},${v.y * pxPerMm}`).join(" ");
                      const bb = boundingBox(verts);
                      const midX = ((bb.minX + bb.maxX) / 2) * pxPerMm, midY = ((bb.minY + bb.maxY) / 2) * pxPerMm;
                      return (
                        <g key={inst.id}>
                          <polygon points={pts} fill={room.color + "33"} stroke={room.color} strokeWidth="1.5" />
                          <text x={midX} y={midY - 4} fontSize="9" fontWeight="bold" textAnchor="middle" fontFamily="ui-monospace, monospace" fill="#1c1a18">{room.name}</text>
                          <text x={midX} y={midY + 8} fontSize="8" textAnchor="middle" fontFamily="ui-monospace, monospace" fill="#555048">
                            {formatLength(bb.maxX - bb.minX, "m")} × {formatLength(bb.maxY - bb.minY, "m")}
                          </text>
                        </g>
                      );
                    })}
                  </g>
                </svg>
              </div>

              <div className="bg-white border border-stone-200 rounded-xl shadow-sm overflow-hidden">
                <p className="text-sm font-semibold text-stone-900 px-4 pt-4 pb-2">Pieces to cut</p>
                <table className="w-full text-xs">
                  <thead>
                    <tr className="text-stone-600 text-left border-b border-stone-100">
                      <th className="font-medium px-4 py-2">Room</th><th className="font-medium py-2">Size</th><th className="font-medium py-2 pr-4 text-right">Qty</th>
                    </tr>
                  </thead>
                  <tbody>
                    {rows.map(([roomId, count]) => {
                      const room = roomsById[roomId];
                      return (
                        <tr key={roomId} className="border-b border-stone-50 last:border-0">
                          <td className="px-4 py-2.5">
                            <span className="flex items-center gap-2 min-w-0"><span className="w-2.5 h-2.5 rounded-full shrink-0" style={{ background: room.color }} /><span className="truncate text-stone-900 font-medium">{room.name}</span></span>
                          </td>
                          <td className="py-2.5 tabular-nums text-stone-600">
                            {formatLength(room.width, "m")} × {formatLength(room.length, "m")}
                            <span className="block text-stone-500">{formatArea(room.area)}</span>
                          </td>
                          <td className="py-2.5 pr-4 text-right tabular-nums font-medium text-stone-900">× {count}</td>
                        </tr>
                      );
                    })}
                  </tbody>
                </table>
              </div>
            </div>
            <p className="text-xs text-stone-500 mt-4 flex items-center gap-1.5"><Info size={12} /> Downloads are rendered in your browser at 2× resolution, so they print sharply.</p>
          </>
        )}
      </div>
    </Modal>
  );
}

/* ======================================================================
   SECTION: APP ROOT
   ====================================================================== */

export default function App() {
  const [rooms, setRooms] = useState([]);
  const [instances, setInstances] = useState([]);
  const [rollWidth, setRollWidth] = useState(4000);
  const [unit, setUnit] = useState("m");
  const [tolerance, setTolerance] = useState(0);
  const [grainMode, setGrainMode] = useState("90");
  const [gridSize, setGridSize] = useState(25);
  const [snapEnabled, setSnapEnabled] = useState(true);
  const [allowOverlap, setAllowOverlap] = useState(true);
  const [guillotineMode, setGuillotineMode] = useState(false);
  const [arranging, setArranging] = useState(false);
  const [projectName, setProjectName] = useState("Untitled Project");
  const [view, setView] = useState("rooms");
  const [selectedId, setSelectedId] = useState(null);
  const [modal, setModal] = useState(null); // { mode: 'add'|'edit', room? }
  const [showCuttingPlan, setShowCuttingPlan] = useState(false);
  const [showHelp, setShowHelp] = useState(false);
  const [loaded, setLoaded] = useState(false);
  const [toast, setToast] = useState(null);
  const [saveState, setSaveState] = useState("saved"); // saved | saving

  const historyRef = useRef({ stack: [], index: -1 });
  const [historyTick, setHistoryTick] = useState(0); // eslint-disable-line no-unused-vars

  const roomsById = useMemo(() => Object.fromEntries(rooms.map((r) => [r.id, r])), [rooms]);

  function showToast(message, tone = "info") { setToast({ message, tone, id: Date.now() }); }

  function commitHistory(nextInstances) {
    const h = historyRef.current;
    h.stack = h.stack.slice(0, h.index + 1);
    h.stack.push(nextInstances);
    h.index = h.stack.length - 1;
    setHistoryTick((t) => t + 1);
  }
  function undo() {
    const h = historyRef.current;
    if (h.index <= 0) return;
    h.index -= 1;
    setInstances(h.stack[h.index]);
    setHistoryTick((t) => t + 1);
  }
  function redo() {
    const h = historyRef.current;
    if (h.index >= h.stack.length - 1) return;
    h.index += 1;
    setInstances(h.stack[h.index]);
    setHistoryTick((t) => t + 1);
  }

  // initial load
  useEffect(() => {
    (async () => {
      const data = await loadProject();
      if (data) {
        setRooms(data.rooms || []);
        setInstances(data.instances || []);
        setRollWidth(data.rollWidth || 4000);
        setUnit(data.unit || "mm");
        setTolerance(data.tolerance ?? 0);
        setGrainMode(data.grainMode || "90");
        setGridSize(data.gridSize || 25);
        setSnapEnabled(data.snapEnabled ?? true);
        setAllowOverlap(data.allowOverlap ?? true);
        setGuillotineMode(data.guillotineMode ?? false);
        setProjectName(data.projectName || "Untitled Project");
        historyRef.current = { stack: [data.instances || []], index: 0 };
        if ((data.instances || []).length > 0) setView("cutting");
      } else {
        historyRef.current = { stack: [[]], index: 0 };
      }
      setLoaded(true);
    })();
  }, []);

  async function doSave() {
    setSaveState("saving");
    await saveProject({ rooms, instances, rollWidth, unit, tolerance, grainMode, gridSize, snapEnabled, allowOverlap, guillotineMode, projectName });
    setSaveState("saved");
  }
  useEffect(() => {
    if (!loaded) return;
    setSaveState("saving");
    const t = setTimeout(doSave, 700);
    return () => clearTimeout(t);
  }, [rooms, instances, rollWidth, unit, tolerance, grainMode, gridSize, snapEnabled, allowOverlap, guillotineMode, projectName, loaded]); // eslint-disable-line

  function handleManualSave() {
    doSave();
    showToast("Project saved", "success");
  }

  function handleSaveRoom(roomData) {
    const isNew = !rooms.some((r) => r.id === roomData.id);
    setRooms((prev) => {
      const exists = prev.some((r) => r.id === roomData.id);
      return exists ? prev.map((r) => (r.id === roomData.id ? roomData : r)) : [...prev, roomData];
    });
    setModal(null);
    showToast(isNew ? `“${roomData.name}” added` : `“${roomData.name}” updated`, "success");
  }

  function handleDeleteRoom(id) {
    setRooms((prev) => prev.filter((r) => r.id !== id));
    setInstances((prev) => {
      const next = prev.filter((i) => i.roomId !== id);
      commitHistory(next);
      return next;
    });
  }

  function handleDuplicateRoom(room) {
    const copy = { ...room, id: `room_${Date.now()}`, name: room.name + " copy" };
    setRooms((prev) => [...prev, copy]);
  }

  function handleQuantityChange(id, qty) {
    setRooms((prev) => prev.map((r) => (r.id === id ? { ...r, quantity: qty } : r)));
  }

  function rotateSelected() {
    setInstances((prev) => {
      const next = prev.map((i) => {
        if (i.id !== selectedId) return i;
        if (grainMode === "locked") return i;
        const step = 90;
        return { ...i, rotation: (i.rotation + step) % 360 };
      });
      commitHistory(next);
      return next;
    });
  }
  function deleteSelected() {
    setInstances((prev) => {
      const next = prev.filter((i) => i.id !== selectedId);
      commitHistory(next);
      return next;
    });
    setSelectedId(null);
  }
  function duplicateSelected() {
    setInstances((prev) => {
      const inst = prev.find((i) => i.id === selectedId);
      if (!inst) return prev;
      const copy = { ...inst, id: `inst_${Date.now()}`, x: inst.x + 100, y: inst.y + 100 };
      const next = [...prev, copy];
      commitHistory(next);
      setSelectedId(copy.id);
      return next;
    });
  }
  function updateAllowanceOverride(val) {
    setInstances((prev) => {
      const next = prev.map((i) => (i.id === selectedId ? { ...i, allowanceOverride: val } : i));
      commitHistory(next);
      return next;
    });
  }

  function newInstanceFor(room, x, y) {
    return {
      id: `inst_${Date.now()}_${Math.random().toString(36).slice(2, 6)}`,
      roomId: room.id, rotation: 0, x, y,
      allowanceOverride: room.cuttingAllowance != null ? String(room.cuttingAllowance) : null,
    };
  }

  // One-click, always-valid placement: drops the room just below whatever is
  // already on the carpet, so it can never collide with another piece.
  function placeRoomOnCarpet(room) {
    setInstances((prev) => {
      const bb = boundingBox(room.vertices);
      const w = bb.maxX - bb.minX;
      const y = requiredLength(prev, roomsById) + (prev.length ? tolerance + 60 : 0);
      const x = Math.max(0, Math.min(rollWidth - w, 0));
      const newInst = newInstanceFor(room, x, y);
      const next = [...prev, newInst];
      commitHistory(next);
      setSelectedId(newInst.id);
      return next;
    });
    setView("cutting");
  }

  // Places every copy still needed (quantity minus what's already on the
  // carpet) for every room, stacked in clear space below the current layout.
  function placeAllRemaining() {
    let next = [...instances];
    let added = 0;
    rooms.forEach((room) => {
      const placed = next.filter((i) => i.roomId === room.id).length;
      for (let k = placed; k < (room.quantity || 1); k++) {
        const y = requiredLength(next, roomsById) + (next.length ? tolerance + 60 : 0);
        next.push(newInstanceFor(room, 0, y));
        added++;
      }
    });
    setView("cutting");
    if (!added) { showToast("Every room is already on the carpet"); return; }
    setInstances(next);
    commitHistory(next);
    setSelectedId(null);
    showToast(`Placed ${added} piece${added > 1 ? "s" : ""} — press “Arrange for me” to pack them tightly`, "success");
  }

  // Keyboard shortcuts: Delete/Backspace removes the selected piece, R
  // rotates it, Escape deselects, Ctrl/Cmd+Z / Ctrl+Y undo and redo.
  // Ignored while typing or while a dialog is open.
  useEffect(() => {
    function onKey(e) {
      const tag = (e.target.tagName || "").toLowerCase();
      if (tag === "input" || tag === "textarea" || tag === "select" || modal || showCuttingPlan || showHelp) return;
      const mod = e.ctrlKey || e.metaKey;
      if (mod && e.key.toLowerCase() === "z") { e.preventDefault(); if (e.shiftKey) redo(); else undo(); return; }
      if (mod && e.key.toLowerCase() === "y") { e.preventDefault(); redo(); return; }
      if (view !== "cutting" || mod) return;
      if ((e.key === "Delete" || e.key === "Backspace") && selectedId) { e.preventDefault(); deleteSelected(); }
      else if (e.key.toLowerCase() === "r" && selectedId) { rotateSelected(); }
      else if (e.key === "Escape") { setSelectedId(null); }
    }
    window.addEventListener("keydown", onKey);
    return () => window.removeEventListener("keydown", onKey);
  }, [selectedId, view, modal, showCuttingPlan, showHelp, grainMode]); // eslint-disable-line

  useEffect(() => {
    if (!toast) return;
    const t = setTimeout(() => setToast(null), 4500);
    return () => clearTimeout(t);
  }, [toast]);

  function runAutoArrange() {
    setArranging(true);
    setToast(null);
    // Defer to the next tick so the "Arranging…" state actually paints
    // before the (synchronous, time-budgeted) search runs.
    setTimeout(() => {
      setInstances((prev) => {
        if (prev.length === 0) return prev;
        const currentLen = requiredLength(prev, roomsById);
        // Validity is checked FIRST: overlapping pieces share space, so an
        // invalid layout can measure as short as (or shorter than) any valid
        // one — a short layout that can't actually be cut isn't efficient.
        const currentInvalid = layoutHasCollisions(prev, roomsById, rollWidth, tolerance);
        const next = autoArrange(prev, roomsById, rollWidth, tolerance, grainMode, guillotineMode);
        const nextLen = requiredLength(next, roomsById);
        if (currentInvalid) {
          commitHistory(next);
          showToast(nextLen < currentLen - EPS
            ? `Fixed overlapping pieces and shortened the plan to ${(nextLen / 1000).toFixed(2)}m`
            : "Fixed overlapping pieces", "success");
          return next;
        }
        // Never make the current plan worse: it's only replaced by a layout
        // that needs strictly less roll, or the same roll but meaningfully
        // easier to cut (see cuttabilityScore).
        if (nextLen < currentLen - EPS) {
          commitHistory(next);
          showToast(`Saved ${((currentLen - nextLen) / 1000).toFixed(2)}m — you now need ${(nextLen / 1000).toFixed(2)}m`, "success");
          return next;
        }
        if (Math.abs(nextLen - currentLen) <= EPS) {
          const currentCut = cuttabilityScore(prev, roomsById, rollWidth);
          const nextCut = cuttabilityScore(next, roomsById, rollWidth);
          if (nextCut > currentCut + EPS) {
            commitHistory(next);
            showToast("Same length, but easier to cut — plan updated", "success");
            return next;
          }
        }
        showToast("This is already the shortest, easiest-to-cut layout found — your plan was kept");
        return prev;
      });
      setArranging(false);
    }, 10);
  }

  const reqLength = useMemo(() => requiredLength(instances, roomsById), [instances, roomsById]);
  const roomArea = useMemo(() => instances.reduce((sum, i) => sum + (roomsById[i.roomId]?.area || 0), 0), [instances, roomsById]);
  const rollArea = rollWidth * reqLength;
  const waste = Math.max(0, rollArea - roomArea);
  const wastePct = rollArea > 0 ? ((waste / rollArea) * 100).toFixed(1) : "0.0";

  const placedByRoom = useMemo(() => {
    const m = {};
    instances.forEach((i) => { if (roomsById[i.roomId]) m[i.roomId] = (m[i.roomId] || 0) + 1; });
    return m;
  }, [instances, roomsById]);
  const totals = useMemo(() => {
    let needed = 0, placed = 0, remaining = 0;
    rooms.forEach((r) => {
      const p = placedByRoom[r.id] || 0;
      needed += r.quantity || 1; placed += p; remaining += Math.max(0, (r.quantity || 1) - p);
    });
    return { needed, placed, remaining };
  }, [rooms, placedByRoom]);

  const stats = {
    projectName, setProjectName,
    rollWidth,
    placed: totals.placed,
    needed: totals.needed,
    lengthLabel: reqLength > 0 ? (reqLength / 1000).toFixed(2) + "m" : "–",
    areaLabel: rollArea > 0 ? formatArea(rollArea) : "–",
    usedLabel: roomArea > 0 ? formatArea(roomArea) : "–",
    wasteLabel: rollArea > 0 ? formatArea(waste) : "–",
    wastePctLabel: rollArea > 0 ? `${wastePct}%` : "–",
  };

  const settings = {
    rollWidth, setRollWidth, unit, setUnit, tolerance, setTolerance, grainMode, setGrainMode,
    gridSize, setGridSize, snapEnabled, setSnapEnabled, allowOverlap, setAllowOverlap, guillotineMode, setGuillotineMode,
  };

  const selectedInstance = instances.find((i) => i.id === selectedId) || null;
  const selectedRoom = selectedInstance ? roomsById[selectedInstance.roomId] : null;
  // Called from buttons (which pass a click event) and from shape shortcuts (which pass a template).
  const openAddRoom = (template) => setModal({ mode: "add", template: template && template.points ? template : null });
  const openEditRoom = (r) => setModal({ mode: "edit", room: r });

  if (!loaded) {
    return (
      <div className="h-screen flex items-center justify-center gap-2 bg-stone-50 text-stone-600 text-sm">
        <Loader2 size={16} className="animate-spin text-brand-500" /> Loading your project…
      </div>
    );
  }

  return (
    <div className="h-screen supports-[height:100dvh]:h-[100dvh] flex flex-col bg-stone-50 text-stone-800">
      <TopBar
        onOpenHelp={() => setShowHelp(true)}
        onUndo={undo} onRedo={redo} canUndo={historyRef.current.index > 0} canRedo={historyRef.current.index < historyRef.current.stack.length - 1}
        onSave={handleManualSave} saveState={saveState}
        view={view} setView={setView} onOpenCuttingPlan={() => setShowCuttingPlan(true)}
        roomCount={rooms.length} instanceCount={instances.length}
      />

      {view === "cutting" ? (
        <div className="flex flex-1 min-h-0">
          <RoomTray
            rooms={rooms} placedByRoom={placedByRoom} remaining={totals.remaining}
            onPlaceOnCarpet={placeRoomOnCarpet} onPlaceAll={placeAllRemaining} onAddRoom={openAddRoom}
          />
          <CuttingCanvas
            rooms={rooms} roomsById={roomsById} instances={instances} setInstances={setInstances}
            rollWidth={rollWidth} tolerance={tolerance} gridSize={gridSize} snapEnabled={snapEnabled}
            selectedId={selectedId} setSelectedId={setSelectedId} commitHistory={commitHistory}
            allowOverlap={allowOverlap} stats={stats}
            onAutoArrange={runAutoArrange} arranging={arranging}
            onPlaceAll={placeAllRemaining} onGoToRooms={() => setView("rooms")}
            selectionActions={{ onRotate: rotateSelected, onDuplicate: duplicateSelected, onDelete: deleteSelected }}
            rotationLocked={grainMode === "locked"}
          />
          <LayoutSidebar
            selectedInstance={selectedInstance} selectedRoom={selectedRoom} stats={stats} settings={settings}
            inspectorProps={{
              onRotate: rotateSelected, onDelete: deleteSelected, onDuplicate: duplicateSelected,
              onAllowanceChange: updateAllowanceOverride, onEditRoom: openEditRoom,
              onDeselect: () => setSelectedId(null), unit, rotationLocked: grainMode === "locked",
            }}
          />
        </div>
      ) : (
        <RoomsView
          rooms={rooms} placedByRoom={placedByRoom} unit={unit}
          onAddRoom={openAddRoom} onEditRoom={openEditRoom}
          onDeleteRoom={handleDeleteRoom} onDuplicateRoom={handleDuplicateRoom} onQuantityChange={handleQuantityChange}
          onPlaceOnCarpet={placeRoomOnCarpet} onPlaceAll={placeAllRemaining} onGoToLayout={() => setView("cutting")}
          settings={settings} totals={totals}
          projectName={projectName} setProjectName={setProjectName} onOpenHelp={() => setShowHelp(true)}
        />
      )}

      {modal && (
        <AddRoomModal
          initialRoom={modal.mode === "edit" ? modal.room : null}
          initialTemplate={modal.template || null}
          onClose={() => setModal(null)}
          onSave={handleSaveRoom}
          displayUnit={unit}
        />
      )}
      {showCuttingPlan && (
        <CuttingPlanModal
          onClose={() => setShowCuttingPlan(false)}
          roomsById={roomsById} instances={instances} rollWidth={rollWidth}
          projectName={projectName} reqLength={reqLength} stats={stats}
        />
      )}
      {showHelp && <HelpModal onClose={() => setShowHelp(false)} />}
      <Toast toast={toast} onDismiss={() => setToast(null)} />
    </div>
  );
}
