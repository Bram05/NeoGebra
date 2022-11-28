project (glad)

add_library (glad STATIC src/glad.c)
target_include_directories (glad PRIVATE "include")
add_subdirectory ("Lib/FreeType")