add_executable (${PROJECT_NAME}  src/main.cpp src/Window.cpp "src/Application.h" "src/Application.cpp" "src/Rendering/Renderer.h" "src/Rendering/Renderer.cpp" "${CMAKE_CURRENT_BINARY_DIR}/Constants.h" "src/Rendering/LineRenderer.h" "src/Rendering/LineRenderer.cpp" "src/Rendering/Shader.h" "src/Rendering/Shader.cpp" "src/UI/WindowUI.h" "src/UI/WindowUI.cpp" "src/UI/EquationUI.h" "src/UI/EquationUI.cpp" "src/UI/UIElement.h" "src/UI/PostulateVerifierResultUI.h" "src/UI/PostulateVerifierResultUI.cpp"  "src/Util.h" "src/Util.cpp" "src/UI/ButtonUI.h" "src/UI/ButtonUI.cpp" "src/UI/UIElement.cpp" "src/Rendering/SquareRenderer.cpp" "src/Rendering/SquareRenderer.h" "src/Objects.h" "src/UI/TextInputField.cpp" "src/UI/TextInputField.h" "src/UI/GraphUI.h" "src/UI/GraphUI.cpp" "src/Rendering/GraphRenderer.cpp" "src/Rendering/GraphRenderer.h" "src/Rendering/GraphShader.cpp" "src/Rendering/GraphShader.h" "src/Rendering/TextRenderer.cpp" "src/Rendering/TextRenderer.h" "src/UI/MenuUI.h" "src/UI/MenuUI.cpp" "src/UI/TabUI.h" "src/UI/TabUI.cpp" "src/UI/PermaButtonUI.h" "src/UI/PermaButtonUI.cpp" "src/UI/KeyboardUI.cpp" "src/UI/KeyboardUI.h" "src/UI/TextInputFieldWithDesc.h" "src/UI/TextInputFieldWithDesc.cpp" "src/Maths/Equation.cpp" "src/Maths/Equation.h" "src/Maths/Model.cpp" "src/Maths/Model.h" "src/UI/ErrorBox.cpp" "src/UI/ErrorBox.h" "src/UI/FPSCounterUI.h" "src/UI/FPSCounterUI.cpp" "src/Rendering/GraphComputeShaderManager.h" "src/Rendering/GraphComputeShaderManager.cpp" "src/UI/MainWindowUI.h" "src/UI/MainWindowUI.cpp" "src/UI/VariableWindowUI.h" "src/UI/VariableWindowUI.cpp" "src/UI/ExtrasWindowUI.cpp" "src/UI/ExtrasWindowUI.h" "src/Maths/PostulateVerifier.cpp" "src/Maths/PostulateVerifier.h" "src/UI/DistanceTestUI.cpp" "src/UI/DistanceTestUI.h")
SetPCH()

target_link_libraries(${PROJECT_NAME} glfw glad stb libz3)
target_include_directories(${PROJECT_NAME} PRIVATE "${CMAKE_HOME_DIRECTORY}/Lib/glad/include" "${CMAKE_HOME_DIRECTORY}/Lib/glfw/include" "${CMAKE_HOME_DIRECTORY}/Lib/Z3/src/api/c++")
target_include_directories(${PROJECT_NAME} PRIVATE "src")
target_include_directories(${PROJECT_NAME} PRIVATE "src" "${CMAKE_HOME_DIRECTORY}/Lib/glm" "${CMAKE_HOME_DIRECTORY}/Lib/stb/include")
target_compile_definitions(${PROJECT_NAME} PRIVATE GLFW_INCLUDE_NONE)

set(inputPath "${CMAKE_HOME_DIRECTORY}/NeoGebra/assets")
cmake_path(NATIVE_PATH inputPath outputPath)
# cmake_path(ABSOLUTE_PATH outputPath OUTPUT_VARIABLE out)
set(AssetsFolder ${outputPath})
configure_file("src/Constants.h.in" "Constants.h")
include_directories("${CMAKE_CURRENT_BINARY_DIR}")

if (CMAKE_VERSION VERSION_GREATER 3.12)
  set_property(TARGET ${PROJECT_NAME} PROPERTY CXX_STANDARD 20)
endif()

if (${CMAKE_BUILD_TYPE} STREQUAL "Debug")
	target_compile_definitions(${PROJECT_NAME} PRIVATE DEBUG)
endif()