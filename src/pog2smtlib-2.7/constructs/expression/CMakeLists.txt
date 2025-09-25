message(STATUS "Processing ${CMAKE_CURRENT_SOURCE_DIR}/CMakeLists.txt")

include_directories(${pog2smtlib-2.7_program_SOURCE_DIR})
set(POG2SMTLIB27_EXPRESSION_SOURCES
  # 5.1 Primary Expressions
  ${CMAKE_CURRENT_SOURCE_DIR}/data.cpp

  # 5.3 Arithmetical Expressions
  ${CMAKE_CURRENT_SOURCE_DIR}/maxint.h ${CMAKE_CURRENT_SOURCE_DIR}/maxint.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/minint.h ${CMAKE_CURRENT_SOURCE_DIR}/minint.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/integerdivision.h ${CMAKE_CURRENT_SOURCE_DIR}/integerdivision.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/floor.h ${CMAKE_CURRENT_SOURCE_DIR}/floor.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/ceiling.h ${CMAKE_CURRENT_SOURCE_DIR}/ceiling.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/toreal.h ${CMAKE_CURRENT_SOURCE_DIR}/toreal.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/predecessor.h ${CMAKE_CURRENT_SOURCE_DIR}/predecessor.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/succ.h ${CMAKE_CURRENT_SOURCE_DIR}/succ.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/exp.h ${CMAKE_CURRENT_SOURCE_DIR}/exp.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/realdivision.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/rexp.h ${CMAKE_CURRENT_SOURCE_DIR}/rexp.cpp

  # 5.4 Arithmetical Expressions (continued)
  ${CMAKE_CURRENT_SOURCE_DIR}/max.h ${CMAKE_CURRENT_SOURCE_DIR}/max.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/min.h ${CMAKE_CURRENT_SOURCE_DIR}/min.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/rmax.h ${CMAKE_CURRENT_SOURCE_DIR}/rmax.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/rmin.h ${CMAKE_CURRENT_SOURCE_DIR}/rmin.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/card.h ${CMAKE_CURRENT_SOURCE_DIR}/card.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/cardinals.h ${CMAKE_CURRENT_SOURCE_DIR}/cardinals.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/generalized_sum.h ${CMAKE_CURRENT_SOURCE_DIR}/generalized_sum.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/generalized_product.h ${CMAKE_CURRENT_SOURCE_DIR}/generalized_product.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/rgeneralized_sum.h ${CMAKE_CURRENT_SOURCE_DIR}/rgeneralized_sum.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/rgeneralized_product.h ${CMAKE_CURRENT_SOURCE_DIR}/rgeneralized_product.cpp

  # 5.5 Expression of Couples
  ${CMAKE_CURRENT_SOURCE_DIR}/maplet.h ${CMAKE_CURRENT_SOURCE_DIR}/maplet.cpp

  # 5.6 Building Sets
  ${CMAKE_CURRENT_SOURCE_DIR}/emptyset.h ${CMAKE_CURRENT_SOURCE_DIR}/emptyset.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/universe.h
  ${CMAKE_CURRENT_SOURCE_DIR}/integer.h ${CMAKE_CURRENT_SOURCE_DIR}/integer.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/real.h ${CMAKE_CURRENT_SOURCE_DIR}/real.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/bool.h ${CMAKE_CURRENT_SOURCE_DIR}/bool.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/nat.h ${CMAKE_CURRENT_SOURCE_DIR}/nat.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/nat1.h ${CMAKE_CURRENT_SOURCE_DIR}/nat1.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/natural.h ${CMAKE_CURRENT_SOURCE_DIR}/natural.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/natural1.h ${CMAKE_CURRENT_SOURCE_DIR}/natural1.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/int.h ${CMAKE_CURRENT_SOURCE_DIR}/int.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/string.h ${CMAKE_CURRENT_SOURCE_DIR}/string.cpp

  # 5.7 Set List Expressions
  ${CMAKE_CURRENT_SOURCE_DIR}/powerset.h ${CMAKE_CURRENT_SOURCE_DIR}/powerset.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/powerset1.h ${CMAKE_CURRENT_SOURCE_DIR}/powerset1.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/interval.h ${CMAKE_CURRENT_SOURCE_DIR}/interval.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/cartesianproduct.h ${CMAKE_CURRENT_SOURCE_DIR}/cartesianproduct.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/set.h ${CMAKE_CURRENT_SOURCE_DIR}/set.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/fin.h ${CMAKE_CURRENT_SOURCE_DIR}/fin.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/fin1.h ${CMAKE_CURRENT_SOURCE_DIR}/fin1.cpp

  # 5.8 Set List Expressions (continued)
  ${CMAKE_CURRENT_SOURCE_DIR}/diff.h ${CMAKE_CURRENT_SOURCE_DIR}/diff.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/union.h ${CMAKE_CURRENT_SOURCE_DIR}/union.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/intersection.h ${CMAKE_CURRENT_SOURCE_DIR}/intersection.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/generalizedunion.h ${CMAKE_CURRENT_SOURCE_DIR}/generalizedunion.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/generalizedintersection.h ${CMAKE_CURRENT_SOURCE_DIR}/generalizedintersection.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/quantified_union.h ${CMAKE_CURRENT_SOURCE_DIR}/quantified_union.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/quantified_inter.h ${CMAKE_CURRENT_SOURCE_DIR}/quantified_inter.cpp

  # 5.9 Record expressions
  ${CMAKE_CURRENT_SOURCE_DIR}/struct.h ${CMAKE_CURRENT_SOURCE_DIR}/struct.cpp

  # 5.10 Set of Relations
  ${CMAKE_CURRENT_SOURCE_DIR}/relations.h ${CMAKE_CURRENT_SOURCE_DIR}/relations.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/total.h ${CMAKE_CURRENT_SOURCE_DIR}/total.cpp

  # 5.11 Expressions of Relations
  ${CMAKE_CURRENT_SOURCE_DIR}/identity.h ${CMAKE_CURRENT_SOURCE_DIR}/identity.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/reverse.h ${CMAKE_CURRENT_SOURCE_DIR}/reverse.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/prj1.h ${CMAKE_CURRENT_SOURCE_DIR}/prj1.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/prj2.h ${CMAKE_CURRENT_SOURCE_DIR}/prj2.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/composition.h ${CMAKE_CURRENT_SOURCE_DIR}/composition.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/directproduct.h ${CMAKE_CURRENT_SOURCE_DIR}/directproduct.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/parallelproduct.h ${CMAKE_CURRENT_SOURCE_DIR}/parallelproduct.cpp

  # 5.12 Expressions of Relations
  ${CMAKE_CURRENT_SOURCE_DIR}/iteration.h ${CMAKE_CURRENT_SOURCE_DIR}/iteration.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/closure.h ${CMAKE_CURRENT_SOURCE_DIR}/closure.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/closure1.h ${CMAKE_CURRENT_SOURCE_DIR}/closure1.cpp

  # 5.13 Expressions of Relations
  ${CMAKE_CURRENT_SOURCE_DIR}/domain.h ${CMAKE_CURRENT_SOURCE_DIR}/domain.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/range.h ${CMAKE_CURRENT_SOURCE_DIR}/range.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/image.h ${CMAKE_CURRENT_SOURCE_DIR}/image.cpp

  # 5.14 Expressions of Relations
  ${CMAKE_CURRENT_SOURCE_DIR}/restriction_domain.h ${CMAKE_CURRENT_SOURCE_DIR}/restriction_domain.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/subtraction_domain.h ${CMAKE_CURRENT_SOURCE_DIR}/subtraction_domain.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/restriction_range.h ${CMAKE_CURRENT_SOURCE_DIR}/restriction_range.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/subtraction_range.h ${CMAKE_CURRENT_SOURCE_DIR}/subtraction_range.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/overwrite.h ${CMAKE_CURRENT_SOURCE_DIR}/overwrite.cpp

  # 5.15 Sets of Functions
  ${CMAKE_CURRENT_SOURCE_DIR}/injection.h ${CMAKE_CURRENT_SOURCE_DIR}/injection.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/surjection.h ${CMAKE_CURRENT_SOURCE_DIR}/surjection.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/bijection.h ${CMAKE_CURRENT_SOURCE_DIR}/bijection.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/functions.h ${CMAKE_CURRENT_SOURCE_DIR}/functions.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/functionspartial.h ${CMAKE_CURRENT_SOURCE_DIR}/functionspartial.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/functionstotal.h ${CMAKE_CURRENT_SOURCE_DIR}/functionstotal.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/partialinjections.h ${CMAKE_CURRENT_SOURCE_DIR}/partialinjections.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/partialsurjections.h ${CMAKE_CURRENT_SOURCE_DIR}/partialsurjections.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/totalbijections.h ${CMAKE_CURRENT_SOURCE_DIR}/totalbijections.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/totalinjections.h ${CMAKE_CURRENT_SOURCE_DIR}/totalinjections.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/totalsurjections.h ${CMAKE_CURRENT_SOURCE_DIR}/totalsurjections.cpp

  # 5.16 Expressions of Functions
  ${CMAKE_CURRENT_SOURCE_DIR}/eval.h ${CMAKE_CURRENT_SOURCE_DIR}/eval.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/intofunction.h ${CMAKE_CURRENT_SOURCE_DIR}/intofunction.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/intorelation.h ${CMAKE_CURRENT_SOURCE_DIR}/intorelation.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/lambda.h ${CMAKE_CURRENT_SOURCE_DIR}/lambda.cpp

  # 5.17 Set of Sequences
  ${CMAKE_CURRENT_SOURCE_DIR}/seq.h ${CMAKE_CURRENT_SOURCE_DIR}/seq.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/seq1.h ${CMAKE_CURRENT_SOURCE_DIR}/seq1.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/iseq.h ${CMAKE_CURRENT_SOURCE_DIR}/iseq.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/iseq1.h ${CMAKE_CURRENT_SOURCE_DIR}/iseq1.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/perm.h ${CMAKE_CURRENT_SOURCE_DIR}/perm.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/emptyseq.h ${CMAKE_CURRENT_SOURCE_DIR}/emptyseq.cpp

  # 5.18 Expressions of Sequences
  ${CMAKE_CURRENT_SOURCE_DIR}/size.h ${CMAKE_CURRENT_SOURCE_DIR}/size.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/first.h ${CMAKE_CURRENT_SOURCE_DIR}/first.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/last.h ${CMAKE_CURRENT_SOURCE_DIR}/last.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/front.h ${CMAKE_CURRENT_SOURCE_DIR}/front.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/tail.h ${CMAKE_CURRENT_SOURCE_DIR}/tail.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/rev.h ${CMAKE_CURRENT_SOURCE_DIR}/rev.cpp

  # 5.19 Expressions of Sequences
  ${CMAKE_CURRENT_SOURCE_DIR}/general_concatenation.h ${CMAKE_CURRENT_SOURCE_DIR}/concatenation.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/insert_in_front.h ${CMAKE_CURRENT_SOURCE_DIR}/insert_in_front.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/insert_at_tail.h ${CMAKE_CURRENT_SOURCE_DIR}/insert_at_tail.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/restrict_in_front.h ${CMAKE_CURRENT_SOURCE_DIR}/restrict_in_front.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/restrict_at_tail.h ${CMAKE_CURRENT_SOURCE_DIR}/restrict_at_tail.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/general_concatenation.h ${CMAKE_CURRENT_SOURCE_DIR}/general_concatenation.cpp

  PARENT_SCOPE
)
