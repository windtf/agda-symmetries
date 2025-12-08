[![website](https://img.shields.io/website?down_color=red&down_message=offline&label=website&up_color=green&up_message=online&url=https%3A%2F%2Fsymmetries.windtfw.com&logo=cloudflare&style=for-the-badge)](https://symmetries.windtfw.com/)
[![build](https://img.shields.io/github/actions/workflow/status/windtf/agda-symmetries/ci-ubuntu.yml?logo=github&style=for-the-badge)](https://github.com/windtf/agda-symmetries/actions/workflows/ci-ubuntu.yml)
[![dependabot](https://img.shields.io/badge/Dependabot-enabled-brightgreen?logo=dependabot&style=for-the-badge)](https://github.com/windtf/agda-symmetries/security/dependabot)
[![license](https://img.shields.io/badge/License-MIT-blue.svg?style=for-the-badge)](https://github.com/windtf/agda-symmetries/blob/main/LICENSE)

This repository contains the artifacts for the [Symmetries in Sorting](https://doi.org/10.5281/zenodo.17829281) paper.
An HTML index of the formalized proofs in the paper can be found [here](https://symmetries.windtfw.com/types25pp.html).

# Abstract

Sorting algorithms are fundamental to computer science, and their correctness criteria are well understood as rearranging elements of a list according to a specified total order on the underlying set of elements. As mathematical functions, they are functions on lists that perform combinatorial operations on the representation of the input list. In this paper, we study sorting algorithms conceptually as abstract sorting functions.

There is a canonical surjection from the free monoid on a set (lists of elements) to the free commutative monoid on the same set (multisets of elements). We show that sorting functions determine a section (right inverse) to this surjection satisfying two axioms, that do not presuppose a total order on the underlying set. Then, we establish an equivalence between (decidable) total orders on the underlying set and correct sorting functions.

The first part of the paper develops concepts from universal algebra from the point of view of functorial signatures, and gives constructions of free monoids and free commutative monoids in (univalent) type theory. Using these constructions, the second part of the paper develops the axiomatization of sorting functions. The paper uses informal mathematical language, and comes with an accompanying formalisation in Cubical Agda.

## Prerequisites

This library has been tested with the following software versions:
 * Agda v2.8.0
 * The Cubical library, [version 0.9](https://github.com/agda/cubical/releases/tag/v0.9) (Jul 30, 2025)

## Type checking the code

Type check the code by running Agda:

```console
$ agda index.agda
```

# License

With the exception of the `papers/` directory, all files in this project are
licensed under the terms of the MIT License, see [LICENSE](LICENSE).

All rights reserved for content under the `papers/` directory.