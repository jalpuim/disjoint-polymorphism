default: coq

all: coq 

coq: systemf language infrastructure subtyping disjointness typing extended dp 

systemf: SystemF.vo 
language: Language.vo
infrastructure: Infrastructure.vo
subtyping: Subtyping.vo 
disjointness: Disjointness.vo 
typing: Typing.vo
extended: Extended.vo
dp: DisjointPolymorphism.vo

SystemF.vo: SystemF.v
	coqc SystemF.v

Language.vo: SystemF.vo Language.v
	coqc Language.v

Infrastructure.vo: Language.vo Infrastructure.v
	coqc Infrastructure.v

Subtyping.vo: Infrastructure.vo Subtyping.v
	coqc Subtyping.v

Disjointness.vo: Subtyping.vo Disjointness.v
	coqc Disjointness.v

Typing.vo: Disjointness.vo Typing.v
	coqc Typing.v

Extended.vo: Typing.vo Extended.v
	coqc Extended.v

DisjointPolymorphism.vo: Extended.vo DisjointPolymorphism.v
	coqc DisjointPolymorphism.v

clean:
	rm -f *.vo *.vio *.glob
