#include "PostulateResult.h"

#include "Rendering/Renderer.h"

PostulateResult::PostulateResult(float leftX, float rightX, float topY, float bottomY, const AdvancedString& name)
	: UIElement(leftX, rightX, topY, bottomY, "PostulateResult"), m_Name{std::make_shared<Text>(name, leftX, rightX, bottomY + 0.02f, 40.0f)},
	m_Result{std::make_shared<Text>(": ---------", leftX + 0.1f,rightX, bottomY + 0.02f, 40.0f)}
{
}

void PostulateResult::RenderPass(Renderer* r)
{
	r->AddToRenderQueue(m_Name);
	r->AddToRenderQueue(m_Result);
	UIElement::RenderPass(r);
}

void PostulateResult::SetResult(PostulateResultValues result)
{
	AdvancedString text;
	switch (result)
	{
	case VALID:
		text = AdvancedString(": valid");
		break;
	case INVALID:
		text = AdvancedString(": invalid");
		break;
	case UNKOWN:
		text = AdvancedString(": unkown");
		break;
	case UNTESTED:
		text = AdvancedString(": untested");
		break;
	case BEINGTESTED:
		text = AdvancedString(": begin tested");
		break;
	}
	m_Result->SetText(text);
}