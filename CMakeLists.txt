cmake_minimum_required (VERSION 3.20)

set(CMAKE_POLICY_DEFAULT_CMP0077 NEW)
cmake_policy(SET CMP0091 NEW)

function(SetPCH)
target_precompile_headers (${PROJECT_NAME} PRIVATE "<chrono>" "<cstdlib>" "<cmath>" "<functional>" "<stack>" "<queue>" "<map>" "<iostream>" "<array>" "<sstream>" "<algorithm>" "<vector>" "<string>" "<tuple>" "<stdexcept>" "<memory>" "<fstream>" "<filesystem>")
endfunction()

# Libraries
# I don't really know why this option in Z3 is forced to be DLL in Debug and static in Release but it has to be the same everywhere so we set it here
#set(CMAKE_MSVC_RUNTIME_LIBRARY "MultiThreaded")
add_subdirectory ("Lib/glad")
set (Z3_BUILD_LIBZ3_SHARED Off)
set (Z3_ENABLE_EXAMPLE_TARGETS Off)
set (Z3_BUILD_DOCUMENTATION Off)
add_subdirectory ("Lib/Z3")
set (GLFW_BUILD_EXAMPLES Off)
set (GLFW_BUILD_TESTS Off)
set (GLFW_BUILD_DOCS Off)
set (GLFW_INSTALL Off)
set (BUILD_SHARED_LIBS Off)
add_subdirectory ("Lib/glfw")
add_subdirectory ("Lib/stb")

# Include sub-projects.
project ("NeoGebra")
add_subdirectory ("NeoGebra")
