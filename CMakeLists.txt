# CMakeList.txt : Top-level CMake project file, do global configuration
# and include sub-projects here.
#
cmake_minimum_required (VERSION 3.8)


# Libraries
add_subdirectory ("Lib/glfw")
add_subdirectory ("PostulateVerifier")
add_subdirectory ("Tests")

# Include sub-projects.
project ("NietEuclidischeGeogebra")
add_subdirectory ("NietEuclidischeGeogebra")
