# Foundations

This is where I publish. The book is *Foundations: Why Structure Is Everything*. A preview — the cover and the first three minted chapters — lives in [writing/books](writing/books/).

Four proofs sit here with it: Hodge, Poincaré, Navier–Stokes, and Birch and Swinnerton-Dyer. Each one has a chapter, a written proof, and Lean 4. Every official statement of the problem is seated or refused.

## How to run

You need git, a compiler toolchain (`cc` / Xcode CLT on a Mac, `build-essential` on Debian), and [elan](https://github.com/leanprover/elan). Elan installs Lean 4 and `lake`. The pin is in `lean-toolchain`: `leanprover/lean4:v4.33.1`. Elan reads that file on the first build.

Install elan (Linux or macOS):

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
source "$HOME/.elan/env"
```

On a Mac you can also `brew install elan`. On Windows, use the installer on the elan page.

Then:

```bash
git clone https://github.com/andersonwilliam85/foundations.git
cd foundations
lake build
```

That builds all four proofs. The first `lake build` will download the pinned Lean. The check is the `Examples.lean` files in each room.

To see the examples run, not only compile:

```bash
lake env lean hodge/Examples.lean
lake env lean poincare/Examples.lean
lake env lean navierstokes/Examples.lean
lake env lean bsd/Examples.lean
```

## The book

- [writing/books/cover.png](writing/books/cover.png)
- [writing/books/Foundations-Preview.pdf](writing/books/Foundations-Preview.pdf)

## The work

I follow the work wherever it goes. The question opens the room. I have sat that way in mathematics and in physics, in economics, in medicine and imaging, in logistics, in writing, in systems and design, and in product — Harmonic Framework, and Neuron.

On Hodge, a hole is a missing relationship: a cycle the shape still owes. The shape is whole if and only if every belonging cycle is present.

On Poincaré, a complete meeting is the sphere, not the world. Closed is the meeting finishing. The dent is a working shape. Ricci is Perelman's path. \(S^3\) is not the world.

On Navier–Stokes, a flow is a lock and its instants. Smooth is every instant whole. Blow-up is a hole before the meeting finishes. Viscosity is in Fefferman's statement. I do not claim the Clay prize from this page.

On Birch and Swinnerton-Dyer, rank and order are two names for one belonging. Sitting generators, and holes at the origin. Zeta is in Wiles's statement. I do not claim a general method.

Who I am, and the dedications, are in [ABOUT.md](ABOUT.md). What has landed is in [CHANGE.md](CHANGE.md). The rest of my writing is at [harmonic-framework.com](https://harmonic-framework.com).

## For the Clay Mathematics Institute

Clay, you can send me a message on LinkedIn: [linkedin.com/in/architect-will](https://www.linkedin.com/in/architect-will).

Thank you for putting this stuff out there.

2026-09-08

— William Christopher Anderson
