# Foundations

This is where I publish. The book is *Foundations: Why Structure Is Everything*. A preview — the cover and the first three minted chapters — lives in [writing/books](writing/books/).

Four proofs sit here with it: hodge, poincare, navier-stokes, and birch and swinnerton-dyer. Each one has a chapter, a written proof, and Lean 4. Every official statement of the problem is seated or refused.

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

That builds all four proofs. The first `lake build` will download the pinned Lean. The Lean check is the `Examples.lean` files. There is no second pytest harness.

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

I follow the work wherever it goes. The question opens the room. I have sat that way in mathematics and in physics, in economics, in medicine and imaging, in logistics, in writing, in systems and design, and in product — Harmonic Framework, and Neuron. I am interested in basically all of it.

hodge, here, is this: a hole is a missing relationship, a cycle the shape still owes. The shape is whole if and only if every belonging cycle is present.

poincare, here, is this: a complete meeting is the sphere, not the world. Closed is the meeting finishing. The dent is a working shape. Ricci is Perelman's path. $S^3$ is not the world.

navier-stokes, here, is this: a flow is a lock and its instants. Smooth is every instant whole. Blow-up is a hole before the meeting finishes. Fields and viscosity can sit on a hole. A flow can be whole with neither. Belonging decides. I solved it.

birch and swinnerton-dyer, here, is this: rank and order are two names for one belonging. Sitting generators, and holes at the origin. Zeta and the letters can sit on a hole. A lock can be whole with none of them. I do not claim a general method. I solved this lock.

Who I am, and the dedications, are in [ABOUT.md](ABOUT.md). What has landed is in [CHANGE.md](CHANGE.md). The rest of my writing is at [harmonic-framework.com](https://harmonic-framework.com).

## Donate

If you want to help, that door is [harmonic-framework.com/donate](https://harmonic-framework.com/donate/).

## For the Clay Mathematics Institute

Clay, you can send me a message on LinkedIn: [linkedin.com/in/architect-will](https://www.linkedin.com/in/architect-will).

Interviews and media go through Harmonic Framework. The dedicated door is being set. GitHub is still a door to the work.

Thank you for putting this stuff out there. The prize will 100% help my family.

If you can find a way to expedite it, that would be great. I am trying to bootstrap my company, and I have been living off savings.

The dedications are in [ABOUT.md](ABOUT.md), where those sentences are allowed to be as long as they actually are.

2026-09-08

— William Christopher Anderson
