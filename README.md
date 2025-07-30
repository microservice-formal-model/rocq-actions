[![DOI](https://zenodo.org/badge/1029218943.svg)](https://doi.org/10.5281/zenodo.16619688)
# rocq-actions
This repository contains the Rocq formalization for theorem 4.1 of the chapter: "A Data-Centric Formal Model
For Event-Based Transactions". The source code is located in the file `actions.v`, and the file is self-contained. No further dependencies are needed.
The source code has been compiled and executed with Coq version 8.20.1 in CoqIDE.

### Mapping of Formalization in Chapter to Rocq
#### Assumptions
- Input actions in Rocq abstract away from variables and contain only the type of the variable
- Output actions abstract away from variables and only contain concrete values of type boolean or nat.
  
These assumptions are made to tailor the formalization to the information needed for the proof in Theorem 4.1.  For the equivalence relation, only the types and the concrete values are necessary to formalize in Rocq. 
#### Mapping
| Chapter                                                       | Rocq                                                                                                                       |
| ------------------------------------------------------------- | -------------------------------------------------------------------------------------------------------------------------- |
| Definition 4.2 (Actions).                                     | `Inductive action`.                                                                                                        |
| Definition 4.4 (Event Signature Equality) $\leftrightarrow_s$. | `Definition eq_in_out`, `Notation =io=`.                                                                                   |
| Definition 4.10 (Equivalence of Actions) $\leftrightarrow_a$. | `Definition act_equiv`, `Notation <-->`.                                                                                    |
| Definition 4.10 $\leftrightarrow_o$.                          | `Definition sig_out_eq`, `Notation <-o->`.                                                                                   |
| Theorem 1.1 $\leftrightarrow_a$ is equivalence relation.      | (i) Reflexivity `Lemma act_equiv_refl` (ii) Symmetry `Theorem act_equiv_sym` (iii) Transitivity `Theorem act_equiv_trans`. |
