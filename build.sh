#!/bin/bash
if [ $1 != "test" ]; then
	echo "(1/2) build compiler"
	echo "        ***BUILD COMPILER***" > build.txt
	echo "" >> build.txt
	echo "\$ bin/parser-generator src/Parser/While.parser" >> build.txt
	bin/parser-generator src/Parser/While.parser &>> build.txt
	Generator=$?
	echo "" >> build.txt
	echo "\$ cabal install --bindir bin/" &>> build.txt
	cabal install --bindir bin/ >> build.txt
	Compiler=$?

	if [ $Compiler != 0 ]
		then
			echo "cabal install finished with error. See build.txt for more details!"
			exit 0
	fi
else
	echo "(1/2) building omittet"
fi
echo "(2/2) run test suit"
echo "" >> build.txt
echo "        ***RUN TEST SUIT***" >>build.txt
echo "" >> build.txt
Tests=0
FailedTests=0
DIR="$( cd $( dirname ${BASH_SOURCE[0]} )  && pwd)"
for f in $DIR/programs/testsuite/*
do
	((Tests++))
	echo "" >> build.txt
	echo "--test \"$f\"" >> build.txt
	rm -r "$f/result"
	mkdir "$f/result"
	echo "  compile \"$f\"" >> build.txt
	bin/compiler -g -d -i -o "$f/result/program" "$f/program.while" &> "$f/result/compiler_output.txt"
	if [ $? != 0 ]
		then
		echo "    Compilation failed: see \"$f/result/compiler_output.txt\" for more details!" >> build.txt
		((FailedTests++))
		continue
	fi
	echo "  run \"$f/result/program\"" >> build.txt
	("$f/result/program" < "$f/in" )&> "$f/result/program_output.txt"
	if [ $? !=  0 ]
		then
		echo "    Execution failed: see \"$f/result/program_output.txt\" for more details!" >> build.txt
		echo "==================================================" >> build.txt
		cat "$f/result/program_output.txt" >> build.txt
		echo "==================================================" >> build.txt
		((FailedTests++))
		continue
	fi
	if ! diff "$f/result/program_output.txt" "$f/out" > /dev/null 
		then
		echo "  !!!Test FAILED!!!: program output is not valid. See \"$f/result/program_output.txt\" or below." >> build.txt
		echo "==================================================" >> build.txt
		cat "$f/result/program_output.txt" >> build.txt
		echo "==================================================" >> build.txt
		((FailedTests++))
		continue
		else
		echo "  OK" >> build.txt
	fi
done

#overview
echo "" >> build.txt
echo "        ***CONCLUSION***" >> build.txt
echo "" >> build.txt

if [ $FailedTests == 0 ]
	then
		echo "All ($Tests) tests ran successful." >> build.txt
	else
		echo "$FailedTests of $Tests tests failed." >> build.txt
fi

if [ $FailedTests == 0 ]
	then
		echo "SUCCESS"
	else
		echo "$FailedTests of $Tests tests failed."
fi
