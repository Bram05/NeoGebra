add_executable (NietEuclidischeGeogebra  src/main.cpp src/Window.cpp "src/Application.h" "src/Application.cpp" "src/Renderer.h" "src/Renderer.cpp" "src/Constants.h" "src/LineRenderer.h" "src/LineRenderer.cpp" "src/Shader.h" "src/Shader.cpp" "src/Maths/Matrix.h"  )

target_precompile_headers (${PROJECT_NAME} REUSE_FROM PostulateVerifier)

target_link_libraries(${PROJECT_NAME} glfw PostulateVerifier glad)
target_include_directories(${PROJECT_NAME} PRIVATE "${CMAKE_HOME_DIRECTORY}/PostulateVerifier/include" "${CMAKE_HOME_DIRECTORY}/Lib/glad/include")
target_include_directories(${PROJECT_NAME} PRIVATE "src")

if (CMAKE_VERSION VERSION_GREATER 3.12)
  set_property(TARGET NietEuclidischeGeogebra PROPERTY CXX_STANDARD 20)
endif()

# TODO: Add tests and install targets if needed.
