OTT_SRC = lambda-iu.ott
OTT_DST = theories/Definitions.v

all: $(OTT_DST) CoqMakefile
	make -f CoqMakefile

$(OTT_DST): $(OTT_SRC)
	ott -i $(OTT_SRC) -o $(OTT_DST)

CoqMakefile: _CoqProject
	coq_makefile -f _CoqProject -o CoqMakefile

clean:
	make -f CoqMakefile clean
	rm -f CoqMakefile CoqMakefile.conf
	rm -f $(OTT_DST)

.PHONY: all clean
