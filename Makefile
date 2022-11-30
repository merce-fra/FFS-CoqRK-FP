-include .coqdep

COQC=coqc

SRC=	Rstruct.v 	\
	Compl.v         \
	Norms.v	\
	FP_prel.v \
	RungeKutta.v \
	Error_loc_to_glob.v \
	Instanciations.v

VO=$(patsubst %.v, %.vo, $(SRC))
RM=rm -rf

COQDEP=coqdep

.PHONY: all clean

all:	$(VO)
	echo $(VO)

%.vo: %.v
	$(COQC) $<

.coqdep deps: $(SRC)
	@ echo "[ INFO ] Calculating source files dependencies"
	@ $(COQDEP) $(SRC) > $@

clean:
	$(RM) *~
	$(RM) *.vo *.vok *.vos *.aux *.glob
	$(RM) .*.aux .*.cache
	$(RM) .coqdep
