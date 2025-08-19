message(STATUS "Processing ${CMAKE_CURRENT_SOURCE_DIR}/CMakeLists.txt")

include_directories(${pog2smtlib27_program_SOURCE_DIR})
set(POG2SMTLIB27_EXPRESSION_SOURCES
  # 5.1 Primary Expressions
  ${CMAKE_CURRENT_SOURCE_DIR}/data.cpp

  # 5.3 Arithmetical Expressions
  ${CMAKE_CURRENT_SOURCE_DIR}/maxint.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/minint.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/integerdivision.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/floor.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/ceiling.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/toreal.cpp

  # 5.4 Arithmetical Expressions (continued)
  ${CMAKE_CURRENT_SOURCE_DIR}/max.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/min.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/card.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/cardinals.cpp

  # 5.5 Expression of Couples
  ${CMAKE_CURRENT_SOURCE_DIR}/maplet.cpp

  # 5.6 Building Sets
  ${CMAKE_CURRENT_SOURCE_DIR}/emptyset.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/universe.h
  ${CMAKE_CURRENT_SOURCE_DIR}/integer.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/real.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/bool.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/nat.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/nat1.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/natural.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/natural1.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/int.cpp

  # 5.7 Set List Expressions
  ${CMAKE_CURRENT_SOURCE_DIR}/powerset.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/powerset1.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/interval.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/cartesianproduct.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/set.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/fin.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/fin1.cpp
  
  # 5.8 Set List Expressions (continued)
  ${CMAKE_CURRENT_SOURCE_DIR}/diff.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/union.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/intersection.cpp 
  ${CMAKE_CURRENT_SOURCE_DIR}/generalizedunion.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/generalizedintersection.cpp 

  # 5.10 Set of Relations
  ${CMAKE_CURRENT_SOURCE_DIR}/relations.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/total.cpp

  # 5.11 Expressions of Relations
  ${CMAKE_CURRENT_SOURCE_DIR}/identity.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/reverse.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/prj1.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/prj2.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/composition.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/directproduct.cpp

  # 5.12 Expressions of Relations
  ${CMAKE_CURRENT_SOURCE_DIR}/iteration.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/closure.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/closure1.cpp

  # 5.13 Expressions of Relations
  ${CMAKE_CURRENT_SOURCE_DIR}/domain.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/range.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/image.cpp

  # 5.14 Expressions of Relations
  ${CMAKE_CURRENT_SOURCE_DIR}/restriction_domain.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/subtraction_domain.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/restriction_range.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/subtraction_range.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/overwrite.cpp

  # 5.15 Sets of Functions
  ${CMAKE_CURRENT_SOURCE_DIR}/injection.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/surjection.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/bijection.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/functions.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/functionspartial.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/functionstotal.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/partialinjections.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/partialsurjections.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/totalbijections.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/totalinjections.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/totalsurjections.cpp

  # 5.16 Expressions of Functions
  ${CMAKE_CURRENT_SOURCE_DIR}/eval.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/intofunction.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/intorelation.cpp

  # 5.17 Set of Sequences 
  ${CMAKE_CURRENT_SOURCE_DIR}/seq.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/seq1.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/iseq.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/iseq1.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/perm.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/emptyseq.cpp

  # 5.18 Expressions of Sequences 
  ${CMAKE_CURRENT_SOURCE_DIR}/size.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/first.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/last.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/front.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/tail.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/rev.cpp

  # 5.19 Expressions of Sequences 
  ${CMAKE_CURRENT_SOURCE_DIR}/concatenation.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/insert_in_front.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/insert_at_tail.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/restrict_in_front.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/restrict_at_tail.cpp
  ${CMAKE_CURRENT_SOURCE_DIR}/general_concatenation.cpp

  PARENT_SCOPE
)
