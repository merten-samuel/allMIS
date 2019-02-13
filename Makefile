include depends

vos = all_MIS_complete.vo all_MIS_unique.vo GenGraph.vo explicit_graph.vo graphs_nondep.vo lGraphMoonTheorem.vo test_cases.vo all_MIS_Refine.vo all_MIS.vo fintype.vo index.vo MIS_basics.vo wf_combinators.vo all_MIS_sound.vo eqtype.vo graph_basics.vo lex_order.vo moon_lemma.vo GenGraphAllMIS.vo

all: $(vos)
.PHONY: depend clean admits

$(vos): %.vo: %.v
	coqc -R . Top $<

depend:
	coqdep *.v > depend

clean:
	rm *.vo *.glob

admits:
	grep -e "admit" *.v
	grep -e "Admitted" *.v


