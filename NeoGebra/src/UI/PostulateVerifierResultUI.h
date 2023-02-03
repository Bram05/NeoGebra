// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html
#pragma once

#include "UIElement.h"
#include "Rendering/LineRenderer.h"
#include "PostulateResult.h"
#include "ButtonUI.h"

class PostulateVerifierResultUI : public UIElement
{
public:
	PostulateVerifierResultUI(float leftX, float rightX, float topY, float bottomY);
	~PostulateVerifierResultUI();

	void VerifyPostulates();

protected:
	void RenderPass(Renderer* r) override;

private:
	std::vector<std::shared_ptr<Line>> m_Lines;
	std::shared_ptr<PostulateResult> m_I2, m_I3, m_B1, m_B2, m_B3, m_C3, m_Distance, m_Parallel;
	int m_TimesTillVerify{-1};
};