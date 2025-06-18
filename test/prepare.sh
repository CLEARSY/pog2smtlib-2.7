#!/bin/bash

BXML_EXE=/opt/atelierb-full-25.05/bin/bxml
POG_EXE=/opt/atelierb-full-25.05/bin/pog
function prepare_pog() {
  infile=$1
  component=`basename $infile .mch`
  echo "component: $component"
  $BXML_EXE -a -i 2 $component.mch > $component.bxml
  $POG_EXE -z pog -p /opt/atelierb-full-25.05/include/pog/paramGOPSoftware.xsl $component.bxml
  mv $component.pog input.pog
  rm $component.bxml $component.pos
}

export -f prepare_pog

TRANSLATOR_EXE=../mybuild/src/pog2smtlib-2.7/pog2smtlib27
SMT_EXE="/usr/bin/cvc4 --lang=smt2 "

function prepare_test_output() {
  id=$1
  $TRANSLATOR_EXE -i input/$id/input.pog -o output > stdout 2> stderr
  echo $? > exitcode
  mv output_0_0.po2 output.smt
  echo "> exitcode:"
  cat exitcode
  echo "> stdout:"
  cat stdout
  echo "> stderr:"
  cat stderr
  echo "> output:"
  cat output.smt
  echo "> CVC4 says "
  $SMT_EXE output.smt
}

export -f prepare_test_output

function install_test_output() {
  id=$1
  destdir=output/reference/$id
  mkdir -p $destdir
  mv exitcode stdout stderr output.smt $destdir
  echo "> contents of $destdir"
  ls -al $destdir
}

export -f install_test_output
