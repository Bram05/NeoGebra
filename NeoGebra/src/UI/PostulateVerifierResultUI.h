// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html
#pragma once

#include "UIElement.h"
#include "Rendering/LineRenderer.h"

class PostulateVerifierResultUI : public UIElement
{
public:
	PostulateVerifierResultUI(double leftX, double rightX, double topY, double bottomY);
	~PostulateVerifierResultUI();

protected:
	void RenderPass(Renderer* r) override;

private:
	std::vector<std::shared_ptr<Line>> m_Lines;
};