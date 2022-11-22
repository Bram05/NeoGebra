add_executable (NietEuclidischeGeogebra  src/main.cpp)

target_precompile_headers (${PROJECT_NAME} REUSE_FROM PostulateVerifier)

target_link_libraries(${PROJECT_NAME} glfw PostulateVerifier)
target_include_directories(${PROJECT_NAME} PRIVATE "${CMAKE_HOME_DIRECTORY}/PostulateVerifier/include")

if (CMAKE_VERSION VERSION_GREATER 3.12)
  set_property(TARGET NietEuclidischeGeogebra PROPERTY CXX_STANDARD 20)
endif()

# TODO: Add tests and install targets if needed.
