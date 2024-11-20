# Pour poursuivre, le travail sur `b2smtlib`

## Fonctionnement du code

Le code de `b2smtlib` se divise en trois modules :

 - `smtlib`, qui contient les fonctions de traduction.
   Au cours du parcours du pog à traduire, une objet `decls` (de classe `PreludeBuilder`) est maintenue à jour. C'est elle qui sera utilisée pour fournir le "prélude", à savoir la définition et l'axiomatisation des symboles de fonction.
 - `PreludeBuilder`, la classe permettant de créer le prélude.
   `PreludeBuilder` renvoie les noms de symboles a utiliser, et met à jour l'ensemble des définitions dont on a besoin. Ces axiomes sont créées à l'aide des schémas contenus dans `axiom_templates`.
 - `axiom_templates`, qui contient les templates d'axiomes et les dépendances.

## Travail restant

Voici quelques pistes de développements pour compléter et améliorer le code de `b2smtlib`.

### Dépendances entre axiomes et symboles polymorphes

En l'état, pour gérer les dépendances entres définitions (la définition d'un symbole a besoin de la définition d''un ou plusieurs autres symboles), on utilise `baxioms::AxiomInstantiator::axiom_dependencies`. Le problème, c'est que cette représentation des dépendances ne tient pas compte des types avec lesquels on utilise les axiomes en question.
 Par exemple, `dom` est une fonction `P (C U V) -> P U`. Mais pour l'utiliser, on a besoin de `mem` (`:`, en B) pour le type `U` (une fonction de type `U, (P U) -> Bool`).

Une première façon de faire cela est d'ajouter à la main les définitions.
C'est ce qui est fait pour ce cas particulier, où on utilise `addAxiom` dans `getAxiomatisation`. Ce faisant, on n'a plus besoin d'une structure pour contenir le graphe des dépendances.

Si on veut utiliser une structure de données pour contenir les dépendances, il faut qu'elle représente les types avec lesquels les symboles sont ajoutés, et qu'on soit capable d'exprimer les types les uns en fonction des autres. Par exemple, pour dom, il faut être capable d'exprimer que `(dom, P (C U V))` dépend de `(mem, U)`, où `U` et `V` sont des types arbitraires.

A noter que certains des symboles ne sont pas polymorphes (par exemple, `pred` ou `NATURAL` sont monomorphes, mais dépendent de mem pour les types `C Int Int` et `Int` respectivement). Il faut être capable de gérer cela.

### Utiliser les enums de BAST

Moins utiliser de string, et davantage de valeurs d'enum (les `Expr::BinaryOp`, etc) dans les appels. (dans `prelude_builder::addSymbol`, `prelude_builder::getAxiomatisation`, `SmtFunDecl::addAxiom`).

### Ne plus utiliser QString

Pour formatter les (schémas) d'axiomes, utiliser autre chose que QString.

Il y a toujours une dépendance à Qt dans POGLoader.

### Ajouter des triggers aux axiomes.

Il faut pour cela skolémiser les formules.
Ça risque de demander un petit travail pour pouvoir générer des noms de variables frais pour les formules quantifiées existentiellement.

Pour l'écriture de triggers, Defourné présente dans sa thèse la stratégie qu'elle a suivi (section 5.3).

### Nary expressions : SET et SEQ

Elle ne sont pas gérées pour l'instant. Les symboles `SET` (ensemble énuméré) et `SEQ` (suite) sont des reliques de `pog2smt`.

Un possibilité pour les ensembles énumérés est d'ajouter un nom d'ensemble (comme c'est fait pour les ensembles définis par compréhension), et de rajouter aux axiomes l'axioms pour l'appartenance.
Par exemple, traduire
```B
myset = {1, 2, 3, 4}
```
en
```SMT-LIB
(declare-const myset (P Int))

(declare-fun mem_0 (Int (P Int)) Bool)

(assert (forall ((x Int))
  (=
    (mem_0 x S)
    (or (= x 1) (= x 2) (= x 3) (= x 4))
  )
))
```

Pour les suites, une possibilité est de construire l'ensemble énuméré associé:
```B
[5, 3, 6] -> {(1 |-> 5), (2 |-> 3), (3 |-> 6)}
```

### Ensembles définis par compréhension

L'implémentation pour les ensembles définis par compréhension (QuantifiedSet) n'est pas complète.
