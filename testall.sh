#!/bin/bash

JAVA_HOME=/opt/java-latest/bin
APRON_HOME=/home/sae/apron

base=$(pwd)

export CLASSPATH=.:$base/soot-2.5.0.jar:$APRON_HOME/japron/apron.jar:$APRON_HOME/japron/gmp.jar:$base/bin
export LD_LIBRARY_PATH=$APRON_HOME/box:$APRON_HOME/octagons:$APRON_HOME/newpolka:$APRON_HOME/apron:$APRON_HOME/japron:$APRON_HOME/japron/gmp

for f in $base/src/T*.java
do
testname=$(basename $f .java)
#echo $testname\:
echo
$JAVA_HOME/java ch.ethz.sae.Verifier $testname | tail -2
done 
