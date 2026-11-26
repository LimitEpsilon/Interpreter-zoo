# Build with Rocq 9.x:  make
all: CoqMakefile
	$(MAKE) -f CoqMakefile

CoqMakefile: _CoqProject
	rocq makefile -f _CoqProject -o CoqMakefile

clean:
	if [ -f CoqMakefile ]; then $(MAKE) -f CoqMakefile clean; fi
	rm -f CoqMakefile CoqMakefile.conf .CoqMakefile.d

.PHONY: all clean
