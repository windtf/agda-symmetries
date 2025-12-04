[![website](https://img.shields.io/website?down_color=red&down_message=offline&label=website&up_color=green&up_message=online&url=https%3A%2F%2Fsymmetries.windtfw.com&logo=cloudflare&style=for-the-badge)](https://symmetries.windtfw.com/)
[![build](https://img.shields.io/github/actions/workflow/status/windtf/agda-symmetries/ci-ubuntu.yml?logo=github&style=for-the-badge)](https://github.com/windtf/agda-symmetries/actions/workflows/ci-ubuntu.yml)
[![dependabot](https://img.shields.io/badge/Dependabot-enabled-brightgreen?logo=dependabot&style=for-the-badge)](https://github.com/windtf/agda-symmetries/security/dependabot)
[![license](https://img.shields.io/badge/License-MIT-blue.svg?style=for-the-badge)](https://github.com/windtf/agda-symmetries/blob/main/LICENSE)

This repository contains the source code, project time log, supervisor meeting minutes, status report,
and dissertation of my individual project for the 4th year of my computing science BSc at the University of Glasgow.

# Abstract

In this project, we study free monoids, free commutative monoids, and their connections with sorting and total
orders. Univalent type theory provides a rigorous framework for implementing these ideas, in the construction
of free algebras using higher inductive types and quotients, and reasoning upto equivalence using categorical
universal properties. The main contributions are a framework for universal algebra (free algebras and their
universal properties), various constructions of free monoids and free commutative monoids (with proofs of their
universal properties), applications to proving combinatorial properties of these constructions, and finally an
axiomatic understanding of sorting.

# Formalization in Agda

This project is formalized using cubical Agda. A HTML rendered version is hosted [here](https://symmetries.windtfw.com/).

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