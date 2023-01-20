project ("PostulateVerifier")

add_library (${PROJECT_NAME} STATIC "src/Model.cpp" "include/PostulateVerifier/PostulateVerifier.h" "src/Equation.cpp" "src/Equation.h")

SetPCH()
target_include_directories(${PROJECT_NAME} PUBLIC "src" "${CMAKE_HOME_DIRECTORY}/Lib/Z3/src/api/c++")
target_link_libraries(${PROJECT_NAME} glfw libz3)

if (CMAKE_VERSION VERSION_GREATER 3.12)
  set_property(TARGET ${PROJECT_NAME} PROPERTY CXX_STANDARD 20)
endif()