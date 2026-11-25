# Tectonic protocol formalization

Tectonic is a stablecoin protocol designed neither to have a minimum reserve threshold for minting stablecoins nor the possibility to depeg. To achieve this, Tectonic uses mechanisms such as triggered redemptions and stability fees. Tectonic is inspired by Djed. 

The stability properties and their proofs from Minimal Djed will be adapted for Tectonic, alongside new lemmas regarding triggered redemptions and leverage. Finally, a formalization will be conducted for Tectonic using the proof assistant Rocq (formerly Coq) in order to raise guarantees and reveal any mistakes or implicit assumptions needed in the proofs. A formalization section in the paper will be added.

## Installation and build

The formalization uses Rocq 9.3.0 and the [RecordUpdate](https://github.com/tchajed/coq-record-update) library.

With [opam](https://opam.ocaml.org/doc/Install.html) installed, create a switch and install the dependencies:

```sh
opam update
opam switch create tectonic-rocq 4.14.2
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install rocq-prover rocq-core=9.3.0 coq-record-update
eval "$(opam env --switch=tectonic-rocq)"
```

From the repository root, check the version and compile the formalization:

```sh
rocq -v
rocq c Tectonic.v
```
