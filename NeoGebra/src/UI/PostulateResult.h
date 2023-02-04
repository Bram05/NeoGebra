#pragma once

#include "UIElement.h"
#include "Rendering/TextRenderer.h"
#include "Maths/PostulateVerifier.h"

class PostulateResult : public UIElement
{
public:
	PostulateResult(float leftX, float rightX, float topY, float bottomY, const AdvancedString& name);
	virtual ~PostulateResult() {}

	virtual void RenderPass(Renderer* r) override;

	void SetResult(PostulateVerifierValues value);
	void SetResult(ParallelType value);
private:
	std::shared_ptr<Text> m_Name, m_Result;
};