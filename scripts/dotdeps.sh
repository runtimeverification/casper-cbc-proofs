#!/bin/sh
(echo "digraph interval_deps {" ;
echo "node [shape=ellipse, style=filled, URL=\"CasperCBC.\N.html\", color=black];";
coqdep -Q . CasperCBC $* | sed -n -e 's,/,.,g;s/[.]vo.*: [^ ]*[.]v//p' |
while read src dst; do
    color=$(echo "$src" | sed -e 's,Lib.*,turquoise,;s,VLSM.Equivocators.*,plum,;s,VLSM.FullNode.*,yellow,;s,VLSM.ListValidator.*,cornflowerblue,;s,VLSM.Liveness.*,green,;s,CBC.*,lightcoral,;s,[A-Z].*,white,')
    echo "\"$src\" [fillcolor=$color];"
    for d in $dst; do
	echo "\"$src\" -> \"${d%.vo}\" ;"
    done
done;
echo "}") | tred
