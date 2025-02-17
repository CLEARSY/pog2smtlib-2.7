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
