add_executable (NietEuclidischeGeogebra  src/main.cpp src/Window.cpp "src/Application.h" "src/Application.cpp" "src/Renderer.h" "src/Renderer.cpp" "src/Constants.h" "src/LineRenderer.h" "src/LineRenderer.cpp" "src/Shader.h" "src/Shader.cpp" "src/Maths/Matrix.h"   "src/UI/WindowUI.h" "src/UI/WindowUI.cpp" "src/UI/EquationUI.h" "src/UI/EquationUI.cpp" "src/UI/UIElement.h" "src/UI/PostulateVerifierResultUI.h" "src/UI/PostulateVerifierResultUI.cpp"  "src/Util.h" "src/Util.cpp" "src/UI/ButtonUI.h" "src/UI/ButtonUI.cpp" "src/UI/UIElement.cpp" "src/SquareRenderer.cpp" "src/SquareRenderer.h" "src/Objects.h" "src/UI/TextInputField.cpp" "src/UI/TextInputField.h" "src/UI/GraphUI.h" "src/UI/GraphUI.cpp")

target_precompile_headers (${PROJECT_NAME} REUSE_FROM PostulateVerifier)

target_link_libraries(${PROJECT_NAME} glfw PostulateVerifier glad freetype)
target_include_directories(${PROJECT_NAME} PRIVATE "${CMAKE_HOME_DIRECTORY}/PostulateVerifier/include" "${CMAKE_HOME_DIRECTORY}/Lib/glad/include" "${CMAKE_HOME_DIRECTORY}/Lib/glfw/include")
target_include_directories(${PROJECT_NAME} PRIVATE "src" "Lib/FreeType/include")

if (CMAKE_VERSION VERSION_GREATER 3.12)
  set_property(TARGET NietEuclidischeGeogebra PROPERTY CXX_STANDARD 20)
endif()

if (${CMAKE_BUILD_TYPE} STREQUAL "Debug")
	target_compile_definitions(${PROJECT_NAME} PRIVATE DEBUG)
endif()