all:compile


compile:
	java -jar ../jtb132di.jar minijava.jj -te
	java -jar ../javacc5.jar minijava-jtb.jj
	javac Main.java

clean:
	rm -r *.class *~
	rm **/*.class
