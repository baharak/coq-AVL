all: AvlTree.vo
SfLib.vo: SfLib.v
	coqc SfLib.v
AvlTree.vo: AvlTree.v SfLib.vo
	coqc AvlTree.v
clean:
	rm -f *.vo *.glob
