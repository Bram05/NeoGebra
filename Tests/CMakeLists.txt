project ("Tests")

add_executable (PostulateVerifierTest src/main.cpp)

target_precompile_headers  (PostulateVerifierTest REUSE_FROM PostulateVerifier)
target_include_directories (PostulateVerifierTest PRIVATE ${CMAKE_HOME_DIRECTORY}/PostulateVerifier/include ${CMAKE_HOME_DIRECTORY}/src)
target_link_libraries (PostulateVerifierTest PostulateVerifier)

if (CMAKE_VERSION VERSION_GREATER 3.12)
  set_property(TARGET PostulateVerifierTest PROPERTY CXX_STANDARD 20)
endif()