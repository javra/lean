set(library_tst_objs $<TARGET_OBJECTS:util> $<TARGET_OBJECTS:library> $<TARGET_OBJECTS:kernel> $<TARGET_OBJECTS:quotient> $<TARGET_OBJECTS:hits> $<TARGET_OBJECTS:inductive> $<TARGET_OBJECTS:sexpr> $<TARGET_OBJECTS:numerics>)
add_executable(expr_lt expr_lt.cpp ${library_tst_objs})
target_link_libraries(expr_lt ${EXTRA_LIBS})
add_test(expr_lt "${CMAKE_CURRENT_BINARY_DIR}/expr_lt")
add_executable(deep_copy deep_copy.cpp ${library_tst_objs})
target_link_libraries(deep_copy ${EXTRA_LIBS})
add_test(deep_copy "${CMAKE_CURRENT_BINARY_DIR}/deep_copy")
add_executable(occurs occurs.cpp ${library_tst_objs})
target_link_libraries(occurs ${EXTRA_LIBS})
add_test(occurs "${CMAKE_CURRENT_BINARY_DIR}/occurs")
add_executable(unifier unifier.cpp ${library_tst_objs})
target_link_libraries(unifier ${EXTRA_LIBS})
add_test(unifier "${CMAKE_CURRENT_BINARY_DIR}/unifier")
add_executable(head_map head_map.cpp ${library_tst_objs})
target_link_libraries(head_map ${EXTRA_LIBS})
add_test(head_map "${CMAKE_CURRENT_BINARY_DIR}/head_map")
