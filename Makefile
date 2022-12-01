build:
	ghc finalProject.hs

test:
	ghc finalProject.hs
	./finalProject > output.real
	diff output.real output.expected

clean:
	rm *.o *.hi finalProject output.real
