add_executable (${PROJECT_NAME}  src/main.cpp src/Window.cpp "src/Application.h" "src/Application.cpp" "src/Renderer.h" "src/Renderer.cpp" "src/Constants.h" "src/LineRenderer.h" "src/LineRenderer.cpp" "src/Shader.h" "src/Shader.cpp" "src/UI/WindowUI.h" "src/UI/WindowUI.cpp" "src/UI/EquationUI.h" "src/UI/EquationUI.cpp" "src/UI/UIElement.h" "src/UI/PostulateVerifierResultUI.h" "src/UI/PostulateVerifierResultUI.cpp"  "src/Util.h" "src/Util.cpp" "src/UI/ButtonUI.h" "src/UI/ButtonUI.cpp" "src/UI/UIElement.cpp" "src/SquareRenderer.cpp" "src/SquareRenderer.h" "src/Objects.h" "src/UI/TextInputField.cpp" "src/UI/TextInputField.h" "src/UI/GraphUI.h" "src/UI/GraphUI.cpp" "src/GraphRenderer.cpp" "src/GraphRenderer.h" "src/GraphShader.cpp" "src/GraphShader.h" "src/TextRenderer.cpp" "src/TextRenderer.h" "src/UI/MenuUI.h" "src/UI/MenuUI.cpp" "src/UI/TabUI.h" "src/UI/TabUI.cpp" "src/UI/PermaButtonUI.h" "src/UI/PermaButtonUI.cpp" "src/UI/KeyboardUI.cpp" "src/UI/KeyboardUI.h" "src/ModelManager.cpp" "src/ModelManager.h"   "src/UI/TextInputFieldWithDesc.h" "src/UI/TextInputFieldWithDesc.cpp")
SetPCH()

target_link_libraries(${PROJECT_NAME} glfw PostulateVerifier glad stb)
target_include_directories(${PROJECT_NAME} PRIVATE "${CMAKE_HOME_DIRECTORY}/PostulateVerifier/include" "${CMAKE_HOME_DIRECTORY}/Lib/glad/include" "${CMAKE_HOME_DIRECTORY}/Lib/glfw/include")
target_include_directories(${PROJECT_NAME} PRIVATE "src")
target_include_directories(${PROJECT_NAME} PRIVATE "src" "${CMAKE_HOME_DIRECTORY}/Lib/glm" "${CMAKE_HOME_DIRECTORY}/Lib/stb/include")
target_compile_definitions(${PROJECT_NAME} PRIVATE GLFW_INCLUDE_NONE)

if (CMAKE_VERSION VERSION_GREATER 3.12)
  set_property(TARGET ${PROJECT_NAME} PROPERTY CXX_STANDARD 20)
endif()

if (${CMAKE_BUILD_TYPE} STREQUAL "Debug")
	target_compile_definitions(${PROJECT_NAME} PRIVATE DEBUG)
endif()