# allMIS
A Coq development for the formalization of graphs and Tsukiyama et al.'s algorithm for finding all maximal independent sets of a graph.

## Build instructions
--------------------
To build the project simply point make at the included makefile.

## Known problems
--------------------
Attempting to compile some of these files in Windows through the CoqIDE can cause the IDE to freeze. However, compilation works problem-free on multiple Linux distributions and OSX.

The project is compatible with Coq 8.7.1.


## File Descriptions
--------------------
* **eqtype**, **fintype**, **index** - An implementation of 'indexed' natural numbers (IX n), the type of natural numbers less than some 'index' n. 
* **lex_order** - An implementation of a lexicographic ordering over sets of natural numbers. 
* **graphs_nondep** - Basic proofs and definitions regarding graphs implemented without the use of dependent types. Additionally, this file contains an implementation (and proofs of correctness) of a program (MKMaximalIndSet) that takes as input an independent set of a graph and produces the lexicographically first maximal independent set that contains the input.
* **graph_basics** - Implements a definition of graphs using dependent types (lGraph) along with an induction scheme using induced subgraphs.
* **MIS_basics** - Extends the definitions and theorems from graphs_nondep to lGraphs and provides some basic proofs relating (maximal) independent sets of induced subgraphs in preparation for the allMIS algorithm.
* **all_MIS** - Implements Tsukiyama et al.'s algorithm (allMIS) for finding all maximal independent sets of a graph and provides a series of lemmas used in the proofs of soundness, completeness and correctness. 
* **all_MIS_sound** - Proof that the output of the allMIS algorithm from all_MIS is sound (contains only maximal independent sets). 
* **all_MIS_complete** - Proof that the output of the allMIS algorithm from all_MIS is complete (every maximal independent set can be found in the output of all_MIS).
* **all_MIS_unique** - Proof that the output of the allMIS algorithm from all_MIS is unique (there are no duplicates in the program's output).
