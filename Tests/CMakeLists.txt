project ("PostulateVerifierTest")

add_executable (${PROJECT_NAME} src/main.cpp)

SetPCH()
target_include_directories (${PROJECT_NAME} PRIVATE ${CMAKE_HOME_DIRECTORY}/PostulateVerifier/include ${CMAKE_HOME_DIRECTORY}/src)
target_link_libraries (${PROJECT_NAME} PostulateVerifier)

if (CMAKE_VERSION VERSION_GREATER 3.12)
  set_property(TARGET ${PROJECT_NAME} PROPERTY CXX_STANDARD 20)
endif()