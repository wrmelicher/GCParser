#!/bin/sh

OUTFILE=`basename $1`.opt
TEMPFILE=.`basename $1`.temp
MIDFILE="$TEMPFILE".gate
echo | cat $1 - | tac $1 | python optimize.py - | tac > $TEMPFILE
# java -cp dist/GCParser.jar:extlibs/commons-io-1.4.jar:extlibs/jargs.jar Test.TestParserFile -g $TEMPFILE
if [ "$2" != "--no-local" ]
then
    java -cp dist/GCParser.jar:extlibs/commons-io-1.4.jar:extlibs/jargs.jar Test.TestParserFile -o $TEMPFILE > $OUTFILE
#    rm $MIDFILE
else
    mv $TEMPFILE $OUTFILE
fi
