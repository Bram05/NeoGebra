project ("stb")

add_library ("stb" STATIC "src/stb.cpp")
target_include_directories ("stb" PRIVATE "include")