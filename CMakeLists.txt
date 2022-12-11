# CMakeList.txt : Top-level CMake project file, do global configuration
# and include sub-projects here.
#
cmake_minimum_required (VERSION 3.8)

set(CMAKE_POLICY_DEFAULT_CMP0077 NEW)

# Libraries
add_subdirectory ("Lib/glad")
set (Z3_BUILD_LIBZ3_SHARED Off)
set (Z3_ENABLE_EXAMPLE_TARGETS Off)
set (Z3_BUILD_DOCUMENTATION Off)
add_subdirectory ("Lib/Z3")
set (ENABLE_AUTO_DOWNLOAD ON)
set (BUILD_BINDINGS_PYTHON OFF)
set (BUILD_BINDINGS_JAVA OFF)
#add_subdirectory ("Lib/cvc5")
set (GLFW_BUILD_EXAMPLES Off)
set (GLFW_BUILD_TESTS Off)
set (GLFW_BUILD_DOCS Off)
set (GLFW_INSTALL Off)
set (BUILD_SHARED_LIBS Off)
add_subdirectory ("Lib/glfw")
add_subdirectory ("Lib/stb")
add_subdirectory ("PostulateVerifier")
add_subdirectory ("Tests")

set (BUILD_SHARED_LIBS false)
add_subdirectory ("Lib/FreeType")

# Include sub-projects.
project ("NietEuclidischeGeogebra")
add_subdirectory ("NietEuclidischeGeogebra")
