// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html
#pragma once

#include "UIElement.h"
#include "Rendering/LineRenderer.h"
#include "Rendering/TextRenderer.h"
#include "Maths/Equation.h"

// The Error box
class ErrorBox : public UIElement
{
public:
	ErrorBox(float leftX, float rightX, float topY, float bottomY);
	~ErrorBox();
	void DisplayError(const AdvancedString& text);
	void RemoveError();

private:
	std::shared_ptr<Text> m_ErrorBoxText;
	std::shared_ptr<Text> m_ErrorText;
	std::vector<std::shared_ptr<Line>> m_Lines;
	std::thread* m_CountingThread{nullptr};
	bool* m_CountingThreadBool{nullptr};

protected:
	void RenderPass(Renderer* r) override;
};