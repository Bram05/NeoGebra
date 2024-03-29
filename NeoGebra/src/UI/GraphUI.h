// Standard library files and some others are automatically included from the precompiled header
// https://cmake.org/cmake/help/latest/command/target_precompile_headers.html
#pragma once

#include "UIElement.h"
#include "Rendering/GraphRenderer.h"
#include "Rendering/GraphComputeShaderManager.h"
#include "Maths/Model.h"
#include "Rendering/TextRenderer.h"
// The middle part of the screen in which graphs are displayed
class GraphUI : public UIElement
{
public:
	GraphUI(float leftX, float rightX, float topY, float bottomY);
	~GraphUI();

	void DeleteGraphs();

protected:
	void RenderPass(Renderer* r) override;
	void ResizeWindow(int width, int height) override;
	void UpdateGraphUI() override;

	virtual void WasClicked(float x, float y) override;
	virtual void DraggedUpdate(float x, float y) override;

private:
	std::vector<std::shared_ptr<Line>> m_Lines;
	std::vector<std::shared_ptr<Graph>> m_Graphs;
	std::vector<std::shared_ptr<Text>> m_Texts;
	
	GraphComputeShaderManager m_ComputeShaderManager;

	float m_MidCoordX, m_MidCoordY, m_UnitLengthPixels;
	float m_MidCoordXBeforeDrag, m_MidCoordYBeforeDrag;
	float m_XBeforeDrag, m_YBeforeDrag;

	void UpdateLines();
	void UpdateGraphs();
	void UpdateCoordinates();
};