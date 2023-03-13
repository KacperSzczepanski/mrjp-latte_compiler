all:
	rm -rf generated
	mkdir generated
	cp src/Latte.cf generated/
	cd generated; /home/students/inf/PUBLIC/MRJP/bin/bnfc -m --functor Latte.cf; make
	cd generated; cp ../src/*.hs .
	cd generated; ghc --make -package mtl Parser.hs -o ../latc_x86
	ln -s latc_x86 latc

clean:
	rm -rf generated latc latc_x86 *.s