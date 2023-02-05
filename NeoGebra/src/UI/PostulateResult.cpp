#include "PostulateResult.h"

#include "Maths/PostulateVerifier.h"

#include "Rendering/Renderer.h"

PostulateResult::PostulateResult(float leftX, float rightX, float topY, float bottomY, const AdvancedString& name)
	: UIElement(leftX, rightX, topY, bottomY, "PostulateResult"), m_Name{ std::make_shared<Text>(name, leftX, rightX, bottomY + 0.02f, 40.0f) },
	m_Result{ std::make_shared<Text>(": ---------", leftX + 0.1f,rightX, bottomY + 0.02f, 40.0f) }
{
}

void PostulateResult::RenderPass(Renderer* r)
{
	r->AddToRenderQueue(m_Name);
	r->AddToRenderQueue(m_Result);
	UIElement::RenderPass(r);
}

void PostulateResult::SetResult(PostulateVerifierValues result)
{
	AdvancedString text;
	switch (result)
	{
	case VALID:
		text = AdvancedString(": valid :)");
		m_Name->m_Colour = { 0.0f,1.0f,0.0f,1.0f };
		m_Result->m_Colour = { 0.0f,1.0f,0.0f,1.0f };
		break;
	case INVALID:
		text = AdvancedString(": invalid");
		m_Name->m_Colour = { 1.0f,0.0f,0.0f,1.0f };
		m_Result->m_Colour = { 1.0f,0.0f,0.0f,1.0f };
		break;
	case UNKOWN:
		text = AdvancedString(": unkown");
		m_Name->m_Colour = { 0.0f,0.0f,0.0f,1.0f };
		m_Result->m_Colour = { 0.0f,0.0f,0.0f,1.0f };
		break;
	case UNTESTED:
		text = AdvancedString(": untested");
		m_Name->m_Colour = { 0.0f,0.0f,0.0f,1.0f };
		m_Result->m_Colour = { 0.0f,0.0f,0.0f,1.0f };
		break;
	case BEINGTESTED:
		text = AdvancedString(": being tested");
		m_Name->m_Colour = { 0.0f,0.0f,0.0f,1.0f };
		m_Result->m_Colour = { 0.0f,0.0f,0.0f,1.0f };
		break;
	}
	m_Result->SetText(text);
}

void PostulateResult::SetResult(ParallelType value)
{
	AdvancedString text;
	switch (value)
	{
	case NORESULT:
		text = AdvancedString(": unkown");
		m_Name->m_Colour = { 0.0f,0.0f,0.0f,1.0f };
		m_Result->m_Colour = { 0.0f,0.0f,0.0f,1.0f };
		break;
	case ELLIPTIC:
		text = AdvancedString(": elliptic");
		m_Name->m_Colour = { 0.0f,0.0f,0.0f,1.0f };
		m_Result->m_Colour = { 0.0f,0.0f,0.0f,1.0f };
		break;
	case EUCLIDEAN:
		text = AdvancedString(": Euclidean");
		m_Name->m_Colour = { 0.0f,0.0f,0.0f,1.0f };
		m_Result->m_Colour = { 0.0f,0.0f,0.0f,1.0f };
		break;
	case HYPERBOLIC:
		text = AdvancedString(": hyperbolic");
		m_Name->m_Colour = { 0.0f,0.0f,0.0f,1.0f };
		m_Result->m_Colour = { 0.0f,0.0f,0.0f,1.0f };
		break;
	default:
		break;
	}
	m_Result->SetText(text);
}
