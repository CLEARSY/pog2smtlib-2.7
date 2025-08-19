#!/bin/bash

#
# - prepare_pog:
#   - description: permet de générer le fichier POG d'une machine.
#   - conditions d'utilisation:
#     - exécuter dans le dossier contenant le code source de la machine
#     - le paramètre est le nom de la machine (nom du fichier sans extension)
#     - les chemins BXML_EXE et POG_EXE doivent être configurés
#
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

TRANSLATOR_EXE=../build/src/pog2smtlib-2.7/pog2smtlib27
SMT_EXE="/usr/bin/cvc5 --tlimit=10000" # timeout in ms

#
# - prepare_test_output:
#   - description: permet de préparer les fichiers de référence pour un test.
#   - conditions d'utilisation:
#     - exécuter dans le dossier racine des tests
#     - le paramètre est le nom du test (nom de la machine contenant le test)
#     - le dossier input/<nom du test> doit exister et contenir un fichier input.pog (cf. fonction prepare_pog)
#     - les chemins TRANSLATOR_EXE et SMT_EXE doivent être configurés
#
function prepare_test_output() {
  id=$1
  $TRANSLATOR_EXE -a 0 0 -i input/$id/input.pog -o output > stdout 2> stderr
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
  echo "> CVC5 says "
  $SMT_EXE output.smt
}

export -f prepare_test_output

#
# - install_test_output:
#   - description: permet de placer correctement les fichiers de référence pour un test.
#   - conditions d'utilisation:
#     - exécuter dans le dossier racine des tests
#     - le paramètre est le nom du test (nom de la machine contenant le test)
#     - il faut auparavant avoir généré les fichiers avec la commande prepare_test_output
#
# une fois le test prêt (entrée et référence), ajouter le test dans le fichier CMakeLists.txt
# et indexer dans le dépôt git.
#
function install_test_output() {
  id=$1
  destdir=output/reference/$id
  mkdir -p $destdir
  mv exitcode stdout stderr output.smt $destdir
  echo "> contents of $destdir"
  ls -al $destdir
}

export -f install_test_output
