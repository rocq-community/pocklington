<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# Pocklington

[![Docker CI][docker-action-shield]][docker-action-link]
[![Contributing][contributing-shield]][contributing-link]
[![Code of Conduct][conduct-shield]][conduct-link]
[![Zulip][zulip-shield]][zulip-link]

[docker-action-shield]: https://github.com/rocq-community/pocklington/actions/workflows/docker-action.yml/badge.svg?branch=master
[docker-action-link]: https://github.com/rocq-community/pocklington/actions/workflows/docker-action.yml

[contributing-shield]: https://img.shields.io/badge/contributions-welcome-%23f7931e.svg
[contributing-link]: https://github.com/coq-community/manifesto/blob/master/CONTRIBUTING.md

[conduct-shield]: https://img.shields.io/badge/%E2%9D%A4-code%20of%20conduct-%23f15a24.svg
[conduct-link]: https://github.com/coq-community/manifesto/blob/master/CODE_OF_CONDUCT.md

[zulip-shield]: https://img.shields.io/badge/chat-on%20zulip-%23c1272d.svg
[zulip-link]: https://coq.zulipchat.com/#narrow/stream/237663-coq-community-devs.20.26.20users



Rocq formalization of Pocklington's criterion for checking primality of
large natural numbers. Includes a formal proof of Fermat's little theorem.

## Meta

- Author(s):
  - Olga Caprotti (initial)
  - Martijn Oostdijk (initial)
- Rocq-community maintainer(s):
  - Pierre Castéran ([**@Casteran**](https://github.com/Casteran))
- License: [GNU Lesser General Public License v2.1 or later](LICENSE)
- Compatible Rocq/Coq versions: 9.0 or later
- Additional dependencies:
  - [Dune](https://dune.build) 3.21 or later
- Rocq/Coq namespace: `Pocklington`
- Related publication(s):
  - [Formal and Efficient Primality Proofs by Use of Computer Algebra Oracles](https://core.ac.uk/download/pdf/82730602.pdf) doi:[10.1006/jsco.2001.0457](https://doi.org/10.1006/jsco.2001.0457)

## Building and installation instructions

The easiest way to install the latest released version of Pocklington
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install coq-pocklington
```

To instead build and install manually, you need to make sure that all the
libraries this development depends on are installed.  The easiest way to do that
is still to rely on opam:

``` shell
git clone https://github.com/rocq-community/pocklington.git
cd pocklington
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install --deps-only .
dune build
dune install
```



