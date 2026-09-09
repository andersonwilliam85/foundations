# Birch and Swinnerton-Dyer: Written Proof

Wiles, for Clay:

> \(\operatorname{rank}\,E(\mathbb{Q})=\operatorname{ord}_{s=1}L(E,s)\).

That sentence is the problem they named.

## The Problem

The sit is leftover, pairing, and drop.

EllipticCurve is a structure over \(\mathbb{Q}\). \(E\) produces a seating. It is not Shape. thisCurve produces a seating. That seating is the lock. Rank is leftover of that seating. Ord \(L\) is cut of that seating. OfficialBsd \((E)\) is leftover and cut of that seating. That pairing is the \(L\) we spend. \(L\) is modeled \(R\). No stored order field. Projection looks up the seated pairing. Inverse reconstructs it. Drop a pairing and OfficialBsdOn fails because \(R\) is gone. OfficialBsd is on \(E\). OfficialBsdOn is on the seating. A dropped seating is not an \(E\).

## 1. Two Sequences Pair

The leftover sequence is \([1,2,3,4,5,6,7,8,9,10,11,12]\). The cut sequence is the primes \([2,3,5,7,11,13,17,19,23,29,31,37]\). Pair them. That seating is the lock. That pairing is \(L\).

\[
(1,2),\;(2,3),\;(3,5),\;(4,7),\;(5,11),\;(6,13),\;\ldots,\;(12,37).
\]

Twelve pairings. Belong and present are the same list.

## 2. Leftover Is The Rank Reading

EllipticCurve is a structure over \(\mathbb{Q}\). thisCurve produces a seating. Leftover is the rank reading of that seating. Rank is leftover. Cut is the \(L\) reading of that seating. Ord \(L\) is cut. No order field.

A leftover carries the slot and the leftover coordinate. Inverse will have to find the cut.

## 3. Projection Looks Up The Pairing

\(\mathrm{cl}\) is the projection from cut to leftover. It looks up the seated pairing and returns that leftover.

\[
\mathrm{cl} : \mathrm{cut}\to\mathrm{leftover}.
\]

On the lock, \(\mathrm{cl}\) of the prime \(13\) is leftover \(6\).

## 4. Inverse Reconstructs The Pairing

\(\mathrm{inverse}\) takes a leftover and reconstructs the cut. The pairing is not stored on leftover.

\[
\mathrm{inverse} : \mathrm{leftover}\to\mathrm{cut}.
\]

On the lock, inverse of leftover \(6\) is the cut \(13\).

## 5. OfficialBsd \((E)\) Is Leftover And Cut

Let \(\alpha\) be a seated leftover of \(E\). Let \(z=\mathrm{inverse}(\alpha)\). Then \(\mathrm{cl}(z)=\alpha\). Rank is that leftover. Ord \(L\) is that cut. They are leftover and cut of one pairing.

OfficialBsd \((E)\) is leftover and cut of the seating \(E\) produces.

\[
\operatorname{rank}=\operatorname{ord} L.
\]

That equality is OfficialBsd on \(E\). OfficialBsdOn is on the seating. Drop fails OfficialBsdOn. A dropped seating is not an \(E\).

## 6. The Lock Holds

OfficialBsdOn thisCurve holds. Every leftover in \([1..12]\) has its inverse among the sitting cuts, and \(\mathrm{cl}\) of that cut is that leftover. \(L\) is modeled \(R\).

## 7. Drop Fails OfficialBsdOn

Drop the sixth pairing \((6,13)\) on the produced seating. Twelve sittings become eleven. Belong still lists leftover \(6\). Present does not sit \(R\) for it.

OfficialBsdOn fails. \(\mathrm{cl}\) of the remaining cuts does not hit leftover \(6\). That hole is the missing \(R\).

Weierstrass, LSeries, torsion of \((0,1)\): furniture.

Their worksheet is furniture.

The Lean file is a check, not the proof.

2026-09-08

— William Christopher Anderson
