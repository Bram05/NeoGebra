project ("PostulateVerifier")

add_library ("PostulateVerifier" STATIC "src/main.cpp" "include/PostulateVerifier/PostulateVerifier.h" "src/Point.h")

target_precompile_headers (${PROJECT_NAME} PRIVATE "<iostream>" "<algorithm>" "<string>" "<tuple>" "<stdexcept>" "<memory>")
target_include_directories(${PROJECT_NAME} PUBLIC "src")
target_link_libraries(${PROJECT_NAME} glfw)

if (CMAKE_VERSION VERSION_GREATER 3.12)
  set_property(TARGET PostulateVerifier PROPERTY CXX_STANDARD 20)
endif()