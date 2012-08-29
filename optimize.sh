#!/bin/sh

OUTFILE=`basename $1`.opt
TEMPFILE=.`basename $1`.temp

echo | cat $1 - | tac $1 | python optimize.py - | tac > $TEMPFILE
if [ "$2" != "--no-local" ]
then
    java -cp dist/GCParser.jar:extlibs/commons-io-1.4.jar:extlibs/jargs.jar Test.TestParserFile -o $TEMPFILE > $OUTFILE
    rm $TEMPFILE
else
    mv $TEMPFILE $OUTFILE
fi

