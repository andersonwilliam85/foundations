# Hodge: Written Proof

Deligne, for Clay:

> On a projective non-singular algebraic variety over $\mathbb{C}$, any Hodge class is a rational linear combination of classes $\mathrm{cl}(Z)$ of algebraic cycles.

A Hodge class, in that paper, is $H^{2p}(X,\mathbb{Q})\cap H^{p,p}(X)$. That sentence is the problem they named.

## The Problem

The sit is leftover, pairing, and drop.

$X$ is ambient $P^n$ plus algebraic cycles. Leftover is produced. Lock pairings take $P^n$. Present comes from those cycles. OfficialHodge is $1\cdot\mathrm{cl}(\mathrm{inverse}\,\alpha)=\alpha$ on that seating. It is not seating $=$ thisLock. Drop a pairing on the produced seating and OfficialHodgeOn fails because $R$ is gone.

## 1. Two Sequences Pair

The leftover sequence is $[1,2,3,4,5,6,7,8,9,10,11,12]$. The cut sequence is the primes $[2,3,5,7,11,13,17,19,23,29,31,37]$. Pair them. That seating is the lock.

$$
(1,2),\;(2,3),\;(3,5),\;(4,7),\;(5,11),\;(6,13),\;\ldots,\;(12,37).
$$

Twelve pairings. Belong and present are the same list.

## 2. Leftover Is Produced

$X$ is ambient $P^n$ plus algebraic cycles. What $X$ owes is the prefix of the lock of length $P^n$. What sits is the owed pairings whose cut is among those cycles. HodgeClass is leftover of that seating at $(p,p)$. No cut field.

A leftover carries the slot and the leftover coordinate. Inverse will have to find the cut.

## 3. Projection Looks Up The Pairing

AlgebraicCycle is Cut. $\mathrm{cl}$ is the projection from cut to leftover. It looks up the seated pairing and returns that leftover.

$$
\mathrm{cl} : \mathrm{cut}\to\mathrm{leftover}.
$$

On the lock, $\mathrm{cl}$ of the prime $13$ is leftover $6$.

## 4. Inverse Reconstructs The Pairing

$\mathrm{inverse}$ takes a leftover and reconstructs the cut. The pairing is not stored on leftover.

$$
\mathrm{inverse} : \mathrm{leftover}\to\mathrm{cut}.
$$

On the lock, inverse of leftover $6$ is the cut $13$.

## 5. OfficialHodge Is One Term On That Seating

Let $\alpha$ be a seated leftover of $X$. Let $z=\mathrm{inverse}(\alpha)$. Then $\mathrm{cl}(z)=\alpha$.

$$
1\cdot\mathrm{cl}(\mathrm{inverse}\,\alpha)=\alpha.
$$

That is a rational linear combination of classes of algebraic cycles. OfficialHodge says it on the seating $X$ produces. It is not seating $=$ thisLock.

## 6. Leftover Holds

I solved leftover. Every leftover produced by that seating has its inverse among the sitting algebraic cycles, and $\mathrm{cl}$ of that cycle is that leftover.

## 7. Drop Fails OfficialHodgeOn

Drop the sixth pairing $(6,13)$ on the produced seating. Twelve sittings become eleven. Belong still lists leftover $6$. Present does not sit $R$ for it.

OfficialHodgeOn fails. $\mathrm{cl}$ of the remaining cuts does not hit leftover $6$. That hole is the missing $R$.

Their worksheet is furniture.

The Lean file is a check, not the proof.

2026-09-09

— William Christopher Anderson
